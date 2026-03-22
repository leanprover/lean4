// Lean compiler output
// Module: Lean.Meta.InstanceNormalForm
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inferInstanceAs"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "wrap"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "normalize instance bodies to constructor-based normal form in `inferInstanceAs` and the default `deriving` handler"};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_object* l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reuseSubInstances"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(10, 196, 243, 125, 230, 240, 101, 207)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "when recursing into sub-instances, reuse existing instances for the target type instead of re-wrapping them, which can be important to avoid non-defeq instance diamonds"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 247, 150, 241, 101, 127, 32, 183)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(154, 83, 182, 188, 30, 204, 110, 119)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "wrap non-reducible instances in auxiliary definitions to fix their types"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 217, 132, 111, 195, 190, 14, 255)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 208, 243, 158, 154, 215, 49, 58)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "wrap data fields in auxiliary definitions to fix their types"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(59, 4, 237, 30, 122, 190, 35, 247)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_data;
static const lean_string_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instanceNormalForm"};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 153, 239, 137, 246, 214, 187, 192)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "InstanceNormalForm"};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 21, 166, 237, 247, 44, 227, 163)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(47, 255, 247, 87, 67, 74, 3, 12)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 214, 207, 188, 255, 52, 193, 89)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(150, 136, 85, 96, 245, 162, 112, 180)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 81, 24, 186, 132, 125, 163, 108)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 9, 213, 84, 12, 241, 213, 223)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(167, 43, 106, 20, 97, 65, 200, 162)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 231, 13, 153, 128, 78, 86, 252)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 42, 205, 166, 86, 40, 201, 52)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2034682956) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(10, 120, 80, 90, 150, 102, 44, 19)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 78, 161, 211, 122, 180, 152, 33)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 99, 74, 33, 199, 2, 218, 255)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(168, 75, 222, 33, 198, 141, 86, 83)}};
static const lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_normalizeInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lean_Meta_normalizeInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_normalizeInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_normalizeInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normalizeInstance___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "did not reduce to constructor application, returning/wrapping as is: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "using existing instance "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof field "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " does not have expected type "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " but "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = ", wrapping in auxiliary theorem: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "instance normal form: incorrect number of arguments for constructor application `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "instance normal form: `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__8 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__8_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not unify with the conclusion of `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__10 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__10_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_normalizeInstance___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_normalizeInstance___closed__0;
static const lean_string_object l_Lean_Meta_normalizeInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "class is "};
static const lean_object* l_Lean_Meta_normalizeInstance___closed__1 = (const lean_object*)&l_Lean_Meta_normalizeInstance___closed__1_value;
static lean_once_cell_t l_Lean_Meta_normalizeInstance___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normalizeInstance___closed__2;
static lean_once_cell_t l_Lean_Meta_normalizeInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_normalizeInstance___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_));
v___x_62_ = ((lean_object*)(l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_));
v___x_63_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0(v___x_60_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_();
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_));
v___x_86_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_));
v___x_87_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_));
v___x_88_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0(v___x_85_, v___x_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4____boxed(lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_));
v___x_111_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_));
v___x_112_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_));
v___x_113_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0(v___x_110_, v___x_111_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4____boxed(lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_();
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_));
v___x_136_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_));
v___x_137_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_));
v___x_138_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4__spec__0(v___x_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4____boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_();
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_201_ = 0;
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_203_ = l_Lean_registerTraceClass(v___x_200_, v___x_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2____boxed(lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_();
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
size_t v_x_2255__boxed_396_; size_t v_x_2256__boxed_397_; lean_object* v_res_398_; 
v_x_2255__boxed_396_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_x_2256__boxed_397_ = lean_unbox_usize(v_x_393_);
lean_dec(v_x_393_);
v_res_398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_391_, v_x_2255__boxed_396_, v_x_2256__boxed_397_, v_x_394_, v_x_395_);
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
lean_object* v___x_410_; lean_object* v_mctx_411_; lean_object* v_cache_412_; lean_object* v_zetaDeltaFVarIds_413_; lean_object* v_postponed_414_; lean_object* v_diag_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_442_; 
v___x_410_ = lean_st_ref_take(v___y_408_);
v_mctx_411_ = lean_ctor_get(v___x_410_, 0);
v_cache_412_ = lean_ctor_get(v___x_410_, 1);
v_zetaDeltaFVarIds_413_ = lean_ctor_get(v___x_410_, 2);
v_postponed_414_ = lean_ctor_get(v___x_410_, 3);
v_diag_415_ = lean_ctor_get(v___x_410_, 4);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_442_ == 0)
{
v___x_417_ = v___x_410_;
v_isShared_418_ = v_isSharedCheck_442_;
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
v_isShared_418_ = v_isSharedCheck_442_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_depth_419_; lean_object* v_levelAssignDepth_420_; lean_object* v_mvarCounter_421_; lean_object* v_lDepth_422_; lean_object* v_decls_423_; lean_object* v_userNames_424_; lean_object* v_lAssignment_425_; lean_object* v_eAssignment_426_; lean_object* v_dAssignment_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_441_; 
v_depth_419_ = lean_ctor_get(v_mctx_411_, 0);
v_levelAssignDepth_420_ = lean_ctor_get(v_mctx_411_, 1);
v_mvarCounter_421_ = lean_ctor_get(v_mctx_411_, 2);
v_lDepth_422_ = lean_ctor_get(v_mctx_411_, 3);
v_decls_423_ = lean_ctor_get(v_mctx_411_, 4);
v_userNames_424_ = lean_ctor_get(v_mctx_411_, 5);
v_lAssignment_425_ = lean_ctor_get(v_mctx_411_, 6);
v_eAssignment_426_ = lean_ctor_get(v_mctx_411_, 7);
v_dAssignment_427_ = lean_ctor_get(v_mctx_411_, 8);
v_isSharedCheck_441_ = !lean_is_exclusive(v_mctx_411_);
if (v_isSharedCheck_441_ == 0)
{
v___x_429_ = v_mctx_411_;
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
lean_inc(v_lDepth_422_);
lean_inc(v_mvarCounter_421_);
lean_inc(v_levelAssignDepth_420_);
lean_inc(v_depth_419_);
lean_dec(v_mctx_411_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(v_eAssignment_426_, v_mvarId_406_, v_val_407_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 7, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_depth_419_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_levelAssignDepth_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_mvarCounter_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_lDepth_422_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_decls_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_userNames_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_lAssignment_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v_dAssignment_427_);
v___x_433_ = v_reuseFailAlloc_440_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_433_);
v___x_435_ = v___x_417_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_cache_412_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_zetaDeltaFVarIds_413_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_postponed_414_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_diag_415_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_st_ref_set(v___y_408_, v___x_435_);
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
v___x_469_ = lean_array_get_borrowed(v___x_468_, v_fst_448_, v_i_453_);
v___x_470_ = lean_unbox(v___x_469_);
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
lean_inc(v_a_495_);
lean_inc_ref(v_a_494_);
lean_inc(v_a_493_);
lean_inc_ref(v_a_492_);
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
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec_ref(v_a_492_);
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
lean_dec(v_a_493_);
return v___x_521_;
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v_fn_497_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
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
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
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
size_t v_x_2658__boxed_599_; size_t v_x_2659__boxed_600_; lean_object* v_res_601_; 
v_x_2658__boxed_599_ = lean_unbox_usize(v_x_595_);
lean_dec(v_x_595_);
v_x_2659__boxed_600_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_res_601_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(v_00_u03b2_593_, v_x_594_, v_x_2658__boxed_599_, v_x_2659__boxed_600_, v_x_597_, v_x_598_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(lean_object* v_opts_630_, lean_object* v_opt_631_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0___boxed(lean_object* v_opts_640_, lean_object* v_opt_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_opts_640_, v_opt_641_);
lean_dec_ref(v_opt_641_);
lean_dec_ref(v_opts_640_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(lean_object* v_kind_644_, lean_object* v___y_645_){
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
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg___boxed(lean_object* v_kind_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v_kind_673_, v___y_674_);
lean_dec(v___y_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1(lean_object* v_kind_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v_kind_677_, v___y_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___boxed(lean_object* v_kind_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1(v_kind_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_691_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__0);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__1);
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
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(lean_object* v_declName_698_, uint8_t v_s_699_, lean_object* v___y_700_, lean_object* v___y_701_){
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
v___x_718_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2);
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
v___x_730_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3);
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
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___boxed(lean_object* v_declName_742_, lean_object* v_s_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
uint8_t v_s_boxed_747_; lean_object* v_res_748_; 
v_s_boxed_747_ = lean_unbox(v_s_743_);
v_res_748_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(v_declName_742_, v_s_boxed_747_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec(v___y_744_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2(lean_object* v_declName_749_, uint8_t v_s_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(v_declName_749_, v_s_750_, v___y_752_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___boxed(lean_object* v_declName_757_, lean_object* v_s_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v_s_boxed_764_; lean_object* v_res_765_; 
v_s_boxed_764_ = lean_unbox(v_s_758_);
v_res_765_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2(v_declName_757_, v_s_boxed_764_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(lean_object* v_cls_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_options_772_; uint8_t v_hasTrace_773_; 
v_options_772_ = lean_ctor_get(v___y_770_, 2);
v_hasTrace_773_ = lean_ctor_get_uint8(v_options_772_, sizeof(void*)*1);
if (v_hasTrace_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_cls_769_);
v___x_774_ = lean_box(v_hasTrace_773_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
else
{
lean_object* v_inheritedTraceOptions_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_inheritedTraceOptions_776_ = lean_ctor_get(v___y_770_, 13);
v___x_777_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___closed__1));
v___x_778_ = l_Lean_Name_append(v___x_777_, v_cls_769_);
v___x_779_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_776_, v_options_772_, v___x_778_);
lean_dec(v___x_778_);
v___x_780_ = lean_box(v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg___boxed(lean_object* v_cls_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_782_, v___y_783_);
lean_dec_ref(v___y_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3(lean_object* v_cls_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_786_, v___y_789_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___boxed(lean_object* v_cls_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3(v_cls_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_unsigned_to_nat(32u);
v___x_801_ = lean_mk_empty_array_with_capacity(v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_803_ = ((size_t)5ULL);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_unsigned_to_nat(32u);
v___x_806_ = lean_mk_empty_array_with_capacity(v___x_805_);
v___x_807_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__0);
v___x_808_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
lean_ctor_set(v___x_808_, 2, v___x_804_);
lean_ctor_set(v___x_808_, 3, v___x_804_);
lean_ctor_set_usize(v___x_808_, 4, v___x_803_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg(lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v_traceState_812_; lean_object* v_traces_813_; lean_object* v___x_814_; lean_object* v_traceState_815_; lean_object* v_env_816_; lean_object* v_nextMacroScope_817_; lean_object* v_ngen_818_; lean_object* v_auxDeclNGen_819_; lean_object* v_cache_820_; lean_object* v_messages_821_; lean_object* v_infoState_822_; lean_object* v_snapshotTasks_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_842_; 
v___x_811_ = lean_st_ref_get(v___y_809_);
v_traceState_812_ = lean_ctor_get(v___x_811_, 4);
lean_inc_ref(v_traceState_812_);
lean_dec(v___x_811_);
v_traces_813_ = lean_ctor_get(v_traceState_812_, 0);
lean_inc_ref(v_traces_813_);
lean_dec_ref(v_traceState_812_);
v___x_814_ = lean_st_ref_take(v___y_809_);
v_traceState_815_ = lean_ctor_get(v___x_814_, 4);
v_env_816_ = lean_ctor_get(v___x_814_, 0);
v_nextMacroScope_817_ = lean_ctor_get(v___x_814_, 1);
v_ngen_818_ = lean_ctor_get(v___x_814_, 2);
v_auxDeclNGen_819_ = lean_ctor_get(v___x_814_, 3);
v_cache_820_ = lean_ctor_get(v___x_814_, 5);
v_messages_821_ = lean_ctor_get(v___x_814_, 6);
v_infoState_822_ = lean_ctor_get(v___x_814_, 7);
v_snapshotTasks_823_ = lean_ctor_get(v___x_814_, 8);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_842_ == 0)
{
v___x_825_ = v___x_814_;
v_isShared_826_ = v_isSharedCheck_842_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_snapshotTasks_823_);
lean_inc(v_infoState_822_);
lean_inc(v_messages_821_);
lean_inc(v_cache_820_);
lean_inc(v_traceState_815_);
lean_inc(v_auxDeclNGen_819_);
lean_inc(v_ngen_818_);
lean_inc(v_nextMacroScope_817_);
lean_inc(v_env_816_);
lean_dec(v___x_814_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_842_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint64_t v_tid_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_840_; 
v_tid_827_ = lean_ctor_get_uint64(v_traceState_815_, sizeof(void*)*1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_traceState_815_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v_traceState_815_, 0);
lean_dec(v_unused_841_);
v___x_829_ = v_traceState_815_;
v_isShared_830_ = v_isSharedCheck_840_;
goto v_resetjp_828_;
}
else
{
lean_dec(v_traceState_815_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_840_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___closed__1);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_831_);
v___x_833_ = v___x_829_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_831_);
lean_ctor_set_uint64(v_reuseFailAlloc_839_, sizeof(void*)*1, v_tid_827_);
v___x_833_ = v_reuseFailAlloc_839_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 4, v___x_833_);
v___x_835_ = v___x_825_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_env_816_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_nextMacroScope_817_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_ngen_818_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v_auxDeclNGen_819_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_838_, 5, v_cache_820_);
lean_ctor_set(v_reuseFailAlloc_838_, 6, v_messages_821_);
lean_ctor_set(v_reuseFailAlloc_838_, 7, v_infoState_822_);
lean_ctor_set(v_reuseFailAlloc_838_, 8, v_snapshotTasks_823_);
v___x_835_ = v_reuseFailAlloc_838_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_st_ref_set(v___y_809_, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v_traces_813_);
return v___x_837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg___boxed(lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg(v___y_843_);
lean_dec(v___y_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11(lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg(v___y_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___boxed(lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11(v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_857_;
}
}
static lean_object* _init_l_Lean_Meta_normalizeInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Meta_normalizeInstance___lam__0___closed__0));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__0(lean_object* v_expectedType_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___lam__0___closed__1, &l_Lean_Meta_normalizeInstance___lam__0___closed__1_once, _init_l_Lean_Meta_normalizeInstance___lam__0___closed__1);
v___x_869_ = l_Lean_MessageData_ofExpr(v_expectedType_861_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__0___boxed(lean_object* v_expectedType_872_, lean_object* v_x_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Meta_normalizeInstance___lam__0(v_expectedType_872_, v_x_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec_ref(v_x_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4(lean_object* v_msgData_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v_env_887_; lean_object* v___x_888_; lean_object* v_mctx_889_; lean_object* v_lctx_890_; lean_object* v_options_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_886_ = lean_st_ref_get(v___y_884_);
v_env_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_env_887_);
lean_dec(v___x_886_);
v___x_888_ = lean_st_ref_get(v___y_882_);
v_mctx_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc_ref(v_mctx_889_);
lean_dec(v___x_888_);
v_lctx_890_ = lean_ctor_get(v___y_881_, 2);
v_options_891_ = lean_ctor_get(v___y_883_, 2);
lean_inc_ref(v_options_891_);
lean_inc_ref(v_lctx_890_);
v___x_892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_892_, 0, v_env_887_);
lean_ctor_set(v___x_892_, 1, v_mctx_889_);
lean_ctor_set(v___x_892_, 2, v_lctx_890_);
lean_ctor_set(v___x_892_, 3, v_options_891_);
v___x_893_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v_msgData_880_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4___boxed(lean_object* v_msgData_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4(v_msgData_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_ref_908_; lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_ref_908_ = lean_ctor_get(v___y_905_, 5);
v___x_909_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4(v_msg_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
lean_inc(v_ref_908_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_ref_908_);
lean_ctor_set(v___x_914_, 1, v_a_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 1);
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg___boxed(lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v_msg_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(size_t v_sz_926_, size_t v_i_927_, lean_object* v_bs_928_, lean_object* v___y_929_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_lt(v_i_927_, v_sz_926_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_bs_928_);
return v___x_932_;
}
else
{
lean_object* v_v_933_; lean_object* v___x_934_; 
v_v_933_ = lean_array_uget_borrowed(v_bs_928_, v_i_927_);
lean_inc(v_v_933_);
v___x_934_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_v_933_, v___y_929_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; lean_object* v_bs_x27_937_; size_t v___x_938_; size_t v___x_939_; lean_object* v___x_940_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref(v___x_934_);
v___x_936_ = lean_unsigned_to_nat(0u);
v_bs_x27_937_ = lean_array_uset(v_bs_928_, v_i_927_, v___x_936_);
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_add(v_i_927_, v___x_938_);
v___x_940_ = lean_array_uset(v_bs_x27_937_, v_i_927_, v_a_935_);
v_i_927_ = v___x_939_;
v_bs_928_ = v___x_940_;
goto _start;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_bs_928_);
v_a_942_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_934_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_934_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg___boxed(lean_object* v_sz_950_, lean_object* v_i_951_, lean_object* v_bs_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
size_t v_sz_boxed_955_; size_t v_i_boxed_956_; lean_object* v_res_957_; 
v_sz_boxed_955_ = lean_unbox_usize(v_sz_950_);
lean_dec(v_sz_950_);
v_i_boxed_956_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_boxed_955_, v_i_boxed_956_, v_bs_952_, v___y_953_);
lean_dec(v___y_953_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg(lean_object* v_ref_958_, lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_fileName_965_; lean_object* v_fileMap_966_; lean_object* v_options_967_; lean_object* v_currRecDepth_968_; lean_object* v_maxRecDepth_969_; lean_object* v_ref_970_; lean_object* v_currNamespace_971_; lean_object* v_openDecls_972_; lean_object* v_initHeartbeats_973_; lean_object* v_maxHeartbeats_974_; lean_object* v_quotContext_975_; lean_object* v_currMacroScope_976_; uint8_t v_diag_977_; lean_object* v_cancelTk_x3f_978_; uint8_t v_suppressElabErrors_979_; lean_object* v_inheritedTraceOptions_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_989_; 
v_fileName_965_ = lean_ctor_get(v___y_962_, 0);
v_fileMap_966_ = lean_ctor_get(v___y_962_, 1);
v_options_967_ = lean_ctor_get(v___y_962_, 2);
v_currRecDepth_968_ = lean_ctor_get(v___y_962_, 3);
v_maxRecDepth_969_ = lean_ctor_get(v___y_962_, 4);
v_ref_970_ = lean_ctor_get(v___y_962_, 5);
v_currNamespace_971_ = lean_ctor_get(v___y_962_, 6);
v_openDecls_972_ = lean_ctor_get(v___y_962_, 7);
v_initHeartbeats_973_ = lean_ctor_get(v___y_962_, 8);
v_maxHeartbeats_974_ = lean_ctor_get(v___y_962_, 9);
v_quotContext_975_ = lean_ctor_get(v___y_962_, 10);
v_currMacroScope_976_ = lean_ctor_get(v___y_962_, 11);
v_diag_977_ = lean_ctor_get_uint8(v___y_962_, sizeof(void*)*14);
v_cancelTk_x3f_978_ = lean_ctor_get(v___y_962_, 12);
v_suppressElabErrors_979_ = lean_ctor_get_uint8(v___y_962_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_980_ = lean_ctor_get(v___y_962_, 13);
v_isSharedCheck_989_ = !lean_is_exclusive(v___y_962_);
if (v_isSharedCheck_989_ == 0)
{
v___x_982_ = v___y_962_;
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_inheritedTraceOptions_980_);
lean_inc(v_cancelTk_x3f_978_);
lean_inc(v_currMacroScope_976_);
lean_inc(v_quotContext_975_);
lean_inc(v_maxHeartbeats_974_);
lean_inc(v_initHeartbeats_973_);
lean_inc(v_openDecls_972_);
lean_inc(v_currNamespace_971_);
lean_inc(v_ref_970_);
lean_inc(v_maxRecDepth_969_);
lean_inc(v_currRecDepth_968_);
lean_inc(v_options_967_);
lean_inc(v_fileMap_966_);
lean_inc(v_fileName_965_);
lean_dec(v___y_962_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_ref_984_; lean_object* v___x_986_; 
v_ref_984_ = l_Lean_replaceRef(v_ref_958_, v_ref_970_);
lean_dec(v_ref_970_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 5, v_ref_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_fileName_965_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_fileMap_966_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_options_967_);
lean_ctor_set(v_reuseFailAlloc_988_, 3, v_currRecDepth_968_);
lean_ctor_set(v_reuseFailAlloc_988_, 4, v_maxRecDepth_969_);
lean_ctor_set(v_reuseFailAlloc_988_, 5, v_ref_984_);
lean_ctor_set(v_reuseFailAlloc_988_, 6, v_currNamespace_971_);
lean_ctor_set(v_reuseFailAlloc_988_, 7, v_openDecls_972_);
lean_ctor_set(v_reuseFailAlloc_988_, 8, v_initHeartbeats_973_);
lean_ctor_set(v_reuseFailAlloc_988_, 9, v_maxHeartbeats_974_);
lean_ctor_set(v_reuseFailAlloc_988_, 10, v_quotContext_975_);
lean_ctor_set(v_reuseFailAlloc_988_, 11, v_currMacroScope_976_);
lean_ctor_set(v_reuseFailAlloc_988_, 12, v_cancelTk_x3f_978_);
lean_ctor_set(v_reuseFailAlloc_988_, 13, v_inheritedTraceOptions_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, sizeof(void*)*14, v_diag_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, sizeof(void*)*14 + 1, v_suppressElabErrors_979_);
v___x_986_ = v_reuseFailAlloc_988_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v_msg_959_, v___y_960_, v___y_961_, v___x_986_, v___y_963_);
lean_dec_ref(v___x_986_);
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg___boxed(lean_object* v_ref_990_, lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg(v_ref_990_, v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v_ref_990_);
return v_res_997_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0(void){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
lean_ctor_set(v___x_1003_, 3, v___x_1001_);
lean_ctor_set(v___x_1003_, 4, v___x_1001_);
lean_ctor_set(v___x_1003_, 5, v___x_1001_);
lean_ctor_set(v___x_1003_, 6, v___x_1001_);
lean_ctor_set(v___x_1003_, 7, v___x_1001_);
lean_ctor_set(v___x_1003_, 8, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(32u);
v___x_1005_ = lean_mk_empty_array_with_capacity(v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4(void){
_start:
{
size_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = ((size_t)5ULL);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_unsigned_to_nat(32u);
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_1009_);
v___x_1011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3);
v___x_1012_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_1010_);
lean_ctor_set(v___x_1012_, 2, v___x_1008_);
lean_ctor_set(v___x_1012_, 3, v___x_1008_);
lean_ctor_set_usize(v___x_1012_, 4, v___x_1007_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1013_ = lean_box(1);
v___x_1014_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4);
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1);
v___x_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
lean_ctor_set(v___x_1016_, 2, v___x_1013_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__6));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__8));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__10));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__12));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__14));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__16));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__18));
v___x_1037_ = l_Lean_stringToMessageData(v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(lean_object* v_msg_1038_, lean_object* v_declHint_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v_env_1043_; uint8_t v___x_1044_; 
v___x_1042_ = lean_st_ref_get(v___y_1040_);
v_env_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc_ref(v_env_1043_);
lean_dec(v___x_1042_);
v___x_1044_ = l_Lean_Name_isAnonymous(v_declHint_1039_);
if (v___x_1044_ == 0)
{
uint8_t v_isExporting_1045_; 
v_isExporting_1045_ = lean_ctor_get_uint8(v_env_1043_, sizeof(void*)*8);
if (v_isExporting_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_dec_ref(v_env_1043_);
lean_dec(v_declHint_1039_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_msg_1038_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
lean_inc_ref(v_env_1043_);
v___x_1047_ = l_Lean_Environment_setExporting(v_env_1043_, v___x_1044_);
lean_inc(v_declHint_1039_);
lean_inc_ref(v___x_1047_);
v___x_1048_ = l_Lean_Environment_contains(v___x_1047_, v_declHint_1039_, v_isExporting_1045_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_env_1043_);
lean_dec(v_declHint_1039_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_msg_1038_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_c_1055_; lean_object* v___x_1056_; 
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2);
v___x_1051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5);
v___x_1052_ = l_Lean_Options_empty;
v___x_1053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1047_);
lean_ctor_set(v___x_1053_, 1, v___x_1050_);
lean_ctor_set(v___x_1053_, 2, v___x_1051_);
lean_ctor_set(v___x_1053_, 3, v___x_1052_);
lean_inc(v_declHint_1039_);
v___x_1054_ = l_Lean_MessageData_ofConstName(v_declHint_1039_, v___x_1044_);
v_c_1055_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1055_, 0, v___x_1053_);
lean_ctor_set(v_c_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1043_, v_declHint_1039_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref(v_env_1043_);
lean_dec(v_declHint_1039_);
v___x_1057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_c_1055_);
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_MessageData_note(v___x_1060_);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_msg_1038_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
else
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1099_; 
v_val_1064_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1066_ = v___x_1056_;
v_isShared_1067_ = v_isSharedCheck_1099_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1056_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1099_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v_mod_1071_; uint8_t v___x_1072_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = l_Lean_Environment_header(v_env_1043_);
lean_dec_ref(v_env_1043_);
v___x_1070_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1069_);
v_mod_1071_ = lean_array_get(v___x_1068_, v___x_1070_, v_val_1064_);
lean_dec(v_val_1064_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = l_Lean_isPrivateName(v_declHint_1039_);
lean_dec(v_declHint_1039_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1073_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_c_1055_);
v___x_1075_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_MessageData_ofName(v_mod_1071_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_MessageData_note(v___x_1080_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_msg_1038_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1082_);
v___x_1084_ = v___x_1066_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_c_1055_);
v___x_1088_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_MessageData_ofName(v_mod_1071_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_MessageData_note(v___x_1093_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_msg_1038_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1095_);
v___x_1097_ = v___x_1066_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1100_; 
lean_dec_ref(v_env_1043_);
lean_dec(v_declHint_1039_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_msg_1038_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___boxed(lean_object* v_msg_1101_, lean_object* v_declHint_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(v_msg_1101_, v_declHint_1102_, v___y_1103_);
lean_dec(v___y_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24(lean_object* v_msg_1106_, lean_object* v_declHint_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1123_; 
v___x_1113_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(v_msg_1106_, v_declHint_1107_, v___y_1111_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1118_ = l_Lean_unknownIdentifierMessageTag;
v___x_1119_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v_a_1114_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1119_);
v___x_1121_ = v___x_1116_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24___boxed(lean_object* v_msg_1124_, lean_object* v_declHint_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24(v_msg_1124_, v_declHint_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(lean_object* v_ref_1132_, lean_object* v_msg_1133_, lean_object* v_declHint_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_a_1141_; lean_object* v___x_1142_; 
v___x_1140_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24(v_msg_1133_, v_declHint_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg(v_ref_1132_, v_a_1141_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg___boxed(lean_object* v_ref_1143_, lean_object* v_msg_1144_, lean_object* v_declHint_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(v_ref_1143_, v_msg_1144_, v_declHint_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v_ref_1143_);
return v_res_1151_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__0));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__2));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(lean_object* v_ref_1158_, lean_object* v_constName_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1165_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_1166_ = 0;
lean_inc(v_constName_1159_);
v___x_1167_ = l_Lean_MessageData_ofConstName(v_constName_1159_, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1165_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(v_ref_1158_, v___x_1170_, v_constName_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1172_, lean_object* v_constName_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(v_ref_1172_, v_constName_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v_ref_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(lean_object* v_constName_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_ref_1186_; lean_object* v___x_1187_; 
v_ref_1186_ = lean_ctor_get(v___y_1183_, 5);
lean_inc(v_ref_1186_);
v___x_1187_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(v_ref_1186_, v_constName_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v_ref_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg___boxed(lean_object* v_constName_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(v_constName_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(lean_object* v_constName_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_env_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_env_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1202_);
lean_dec(v___x_1201_);
v___x_1203_ = 0;
lean_inc(v_constName_1195_);
v___x_1204_ = l_Lean_Environment_find_x3f(v_env_1202_, v_constName_1195_, v___x_1203_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(v_constName_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1205_;
}
else
{
lean_object* v_val_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v___y_1198_);
lean_dec(v_constName_1195_);
v_val_1206_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1204_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_val_1206_);
lean_dec(v___x_1204_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 0);
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_val_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5___boxed(lean_object* v_constName_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(v_constName_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(lean_object* v___x_1221_, lean_object* v_a_1222_, lean_object* v_____r_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1221_, v_a_1222_, v___y_1225_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1238_);
v___x_1231_ = v___x_1229_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = lean_box(0);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
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
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_a_1239_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1229_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1229_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2___boxed(lean_object* v___x_1247_, lean_object* v_a_1248_, lean_object* v_____r_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_1247_, v_a_1248_, v_____r_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(lean_object* v_a_1256_, lean_object* v___x_1257_, lean_object* v_____r_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_enableRealizationsForConst(v_a_1256_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1272_; 
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1273_);
v___x_1266_ = v___x_1264_;
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
else
{
lean_dec(v___x_1264_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1272_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1257_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1264_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1264_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0___boxed(lean_object* v_a_1282_, lean_object* v___x_1283_, lean_object* v_____r_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_1282_, v___x_1283_, v_____r_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1290_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1291_; double v___x_1292_; 
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_float_of_nat(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(lean_object* v_cls_1296_, lean_object* v_msg_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_ref_1303_; lean_object* v___x_1304_; lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1349_; 
v_ref_1303_ = lean_ctor_get(v___y_1300_, 5);
v___x_1304_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4(v_msg_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1349_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1349_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v_traceState_1310_; lean_object* v_env_1311_; lean_object* v_nextMacroScope_1312_; lean_object* v_ngen_1313_; lean_object* v_auxDeclNGen_1314_; lean_object* v_cache_1315_; lean_object* v_messages_1316_; lean_object* v_infoState_1317_; lean_object* v_snapshotTasks_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1348_; 
v___x_1309_ = lean_st_ref_take(v___y_1301_);
v_traceState_1310_ = lean_ctor_get(v___x_1309_, 4);
v_env_1311_ = lean_ctor_get(v___x_1309_, 0);
v_nextMacroScope_1312_ = lean_ctor_get(v___x_1309_, 1);
v_ngen_1313_ = lean_ctor_get(v___x_1309_, 2);
v_auxDeclNGen_1314_ = lean_ctor_get(v___x_1309_, 3);
v_cache_1315_ = lean_ctor_get(v___x_1309_, 5);
v_messages_1316_ = lean_ctor_get(v___x_1309_, 6);
v_infoState_1317_ = lean_ctor_get(v___x_1309_, 7);
v_snapshotTasks_1318_ = lean_ctor_get(v___x_1309_, 8);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1320_ = v___x_1309_;
v_isShared_1321_ = v_isSharedCheck_1348_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_snapshotTasks_1318_);
lean_inc(v_infoState_1317_);
lean_inc(v_messages_1316_);
lean_inc(v_cache_1315_);
lean_inc(v_traceState_1310_);
lean_inc(v_auxDeclNGen_1314_);
lean_inc(v_ngen_1313_);
lean_inc(v_nextMacroScope_1312_);
lean_inc(v_env_1311_);
lean_dec(v___x_1309_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1348_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
uint64_t v_tid_1322_; lean_object* v_traces_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1347_; 
v_tid_1322_ = lean_ctor_get_uint64(v_traceState_1310_, sizeof(void*)*1);
v_traces_1323_ = lean_ctor_get(v_traceState_1310_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_traceState_1310_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1325_ = v_traceState_1310_;
v_isShared_1326_ = v_isSharedCheck_1347_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_traces_1323_);
lean_dec(v_traceState_1310_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1347_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; double v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0);
v___x_1329_ = 0;
v___x_1330_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__1));
v___x_1331_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1331_, 0, v_cls_1296_);
lean_ctor_set(v___x_1331_, 1, v___x_1327_);
lean_ctor_set(v___x_1331_, 2, v___x_1330_);
lean_ctor_set_float(v___x_1331_, sizeof(void*)*3, v___x_1328_);
lean_ctor_set_float(v___x_1331_, sizeof(void*)*3 + 8, v___x_1328_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*3 + 16, v___x_1329_);
v___x_1332_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__2));
v___x_1333_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v_a_1305_);
lean_ctor_set(v___x_1333_, 2, v___x_1332_);
lean_inc(v_ref_1303_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_ref_1303_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = l_Lean_PersistentArray_push___redArg(v_traces_1323_, v___x_1334_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1335_);
v___x_1337_ = v___x_1325_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1335_);
lean_ctor_set_uint64(v_reuseFailAlloc_1346_, sizeof(void*)*1, v_tid_1322_);
v___x_1337_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 4, v___x_1337_);
v___x_1339_ = v___x_1320_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_env_1311_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_nextMacroScope_1312_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_ngen_1313_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_auxDeclNGen_1314_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1345_, 5, v_cache_1315_);
lean_ctor_set(v_reuseFailAlloc_1345_, 6, v_messages_1316_);
lean_ctor_set(v_reuseFailAlloc_1345_, 7, v_infoState_1317_);
lean_ctor_set(v_reuseFailAlloc_1345_, 8, v_snapshotTasks_1318_);
v___x_1339_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1340_ = lean_st_ref_set(v___y_1301_, v___x_1339_);
v___x_1341_ = lean_box(0);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1341_);
v___x_1343_ = v___x_1307_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___boxed(lean_object* v_cls_1350_, lean_object* v_msg_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_1350_, v_msg_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(lean_object* v_a_1358_, lean_object* v___x_1359_, uint8_t v___x_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v_____r_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_box(0);
lean_inc(v___y_1365_);
v___x_1370_ = l_Lean_Meta_mkAuxTheorem(v_a_1358_, v___x_1359_, v___x_1360_, v___x_1369_, v___x_1360_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1372_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1361_, v_a_1371_, v___y_1365_);
lean_dec(v___y_1365_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1380_; 
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1372_, 0);
lean_dec(v_unused_1381_);
v___x_1374_ = v___x_1372_;
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v___x_1372_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1362_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
v_a_1382_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1372_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1372_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v___y_1365_);
lean_dec(v___x_1361_);
v_a_1390_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1370_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1370_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3___boxed(lean_object* v_a_1398_, lean_object* v___x_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v___x_1402_, lean_object* v_____r_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
uint8_t v___x_88831__boxed_1409_; lean_object* v_res_1410_; 
v___x_88831__boxed_1409_ = lean_unbox(v___x_1400_);
v_res_1410_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_1398_, v___x_1399_, v___x_88831__boxed_1409_, v___x_1401_, v___x_1402_, v_____r_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
if (lean_obj_tag(v_a_1411_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = l_List_reverse___redArg(v_a_1412_);
return v___x_1413_;
}
else
{
lean_object* v_head_1414_; lean_object* v_tail_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1424_; 
v_head_1414_ = lean_ctor_get(v_a_1411_, 0);
v_tail_1415_ = lean_ctor_get(v_a_1411_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_a_1411_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1417_ = v_a_1411_;
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_tail_1415_);
lean_inc(v_head_1414_);
lean_dec(v_a_1411_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = l_Lean_MessageData_ofExpr(v_head_1414_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v_a_1412_);
lean_ctor_set(v___x_1417_, 0, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_a_1412_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
v_a_1411_ = v_tail_1415_;
v_a_1412_ = v___x_1421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21(size_t v_sz_1425_, size_t v_i_1426_, lean_object* v_bs_1427_){
_start:
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_usize_dec_lt(v_i_1426_, v_sz_1425_);
if (v___x_1428_ == 0)
{
return v_bs_1427_;
}
else
{
lean_object* v_v_1429_; lean_object* v_msg_1430_; lean_object* v___x_1431_; lean_object* v_bs_x27_1432_; size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v_v_1429_ = lean_array_uget_borrowed(v_bs_1427_, v_i_1426_);
v_msg_1430_ = lean_ctor_get(v_v_1429_, 1);
lean_inc_ref(v_msg_1430_);
v___x_1431_ = lean_unsigned_to_nat(0u);
v_bs_x27_1432_ = lean_array_uset(v_bs_1427_, v_i_1426_, v___x_1431_);
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1426_, v___x_1433_);
v___x_1435_ = lean_array_uset(v_bs_x27_1432_, v_i_1426_, v_msg_1430_);
v_i_1426_ = v___x_1434_;
v_bs_1427_ = v___x_1435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21___boxed(lean_object* v_sz_1437_, lean_object* v_i_1438_, lean_object* v_bs_1439_){
_start:
{
size_t v_sz_boxed_1440_; size_t v_i_boxed_1441_; lean_object* v_res_1442_; 
v_sz_boxed_1440_ = lean_unbox_usize(v_sz_1437_);
lean_dec(v_sz_1437_);
v_i_boxed_1441_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21(v_sz_boxed_1440_, v_i_boxed_1441_, v_bs_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19(lean_object* v_oldTraces_1443_, lean_object* v_data_1444_, lean_object* v_ref_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_fileName_1452_; lean_object* v_fileMap_1453_; lean_object* v_options_1454_; lean_object* v_currRecDepth_1455_; lean_object* v_maxRecDepth_1456_; lean_object* v_ref_1457_; lean_object* v_currNamespace_1458_; lean_object* v_openDecls_1459_; lean_object* v_initHeartbeats_1460_; lean_object* v_maxHeartbeats_1461_; lean_object* v_quotContext_1462_; lean_object* v_currMacroScope_1463_; uint8_t v_diag_1464_; lean_object* v_cancelTk_x3f_1465_; uint8_t v_suppressElabErrors_1466_; lean_object* v_inheritedTraceOptions_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1522_; 
v_fileName_1452_ = lean_ctor_get(v___y_1449_, 0);
v_fileMap_1453_ = lean_ctor_get(v___y_1449_, 1);
v_options_1454_ = lean_ctor_get(v___y_1449_, 2);
v_currRecDepth_1455_ = lean_ctor_get(v___y_1449_, 3);
v_maxRecDepth_1456_ = lean_ctor_get(v___y_1449_, 4);
v_ref_1457_ = lean_ctor_get(v___y_1449_, 5);
v_currNamespace_1458_ = lean_ctor_get(v___y_1449_, 6);
v_openDecls_1459_ = lean_ctor_get(v___y_1449_, 7);
v_initHeartbeats_1460_ = lean_ctor_get(v___y_1449_, 8);
v_maxHeartbeats_1461_ = lean_ctor_get(v___y_1449_, 9);
v_quotContext_1462_ = lean_ctor_get(v___y_1449_, 10);
v_currMacroScope_1463_ = lean_ctor_get(v___y_1449_, 11);
v_diag_1464_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*14);
v_cancelTk_x3f_1465_ = lean_ctor_get(v___y_1449_, 12);
v_suppressElabErrors_1466_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1467_ = lean_ctor_get(v___y_1449_, 13);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___y_1449_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1469_ = v___y_1449_;
v_isShared_1470_ = v_isSharedCheck_1522_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_inheritedTraceOptions_1467_);
lean_inc(v_cancelTk_x3f_1465_);
lean_inc(v_currMacroScope_1463_);
lean_inc(v_quotContext_1462_);
lean_inc(v_maxHeartbeats_1461_);
lean_inc(v_initHeartbeats_1460_);
lean_inc(v_openDecls_1459_);
lean_inc(v_currNamespace_1458_);
lean_inc(v_ref_1457_);
lean_inc(v_maxRecDepth_1456_);
lean_inc(v_currRecDepth_1455_);
lean_inc(v_options_1454_);
lean_inc(v_fileMap_1453_);
lean_inc(v_fileName_1452_);
lean_dec(v___y_1449_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1522_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v_traceState_1472_; lean_object* v_traces_1473_; lean_object* v_ref_1474_; lean_object* v___x_1476_; 
v___x_1471_ = lean_st_ref_get(v___y_1450_);
v_traceState_1472_ = lean_ctor_get(v___x_1471_, 4);
lean_inc_ref(v_traceState_1472_);
lean_dec(v___x_1471_);
v_traces_1473_ = lean_ctor_get(v_traceState_1472_, 0);
lean_inc_ref(v_traces_1473_);
lean_dec_ref(v_traceState_1472_);
v_ref_1474_ = l_Lean_replaceRef(v_ref_1445_, v_ref_1457_);
lean_dec(v_ref_1457_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 5, v_ref_1474_);
v___x_1476_ = v___x_1469_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_fileName_1452_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_fileMap_1453_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_options_1454_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_currRecDepth_1455_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_maxRecDepth_1456_);
lean_ctor_set(v_reuseFailAlloc_1521_, 5, v_ref_1474_);
lean_ctor_set(v_reuseFailAlloc_1521_, 6, v_currNamespace_1458_);
lean_ctor_set(v_reuseFailAlloc_1521_, 7, v_openDecls_1459_);
lean_ctor_set(v_reuseFailAlloc_1521_, 8, v_initHeartbeats_1460_);
lean_ctor_set(v_reuseFailAlloc_1521_, 9, v_maxHeartbeats_1461_);
lean_ctor_set(v_reuseFailAlloc_1521_, 10, v_quotContext_1462_);
lean_ctor_set(v_reuseFailAlloc_1521_, 11, v_currMacroScope_1463_);
lean_ctor_set(v_reuseFailAlloc_1521_, 12, v_cancelTk_x3f_1465_);
lean_ctor_set(v_reuseFailAlloc_1521_, 13, v_inheritedTraceOptions_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*14, v_diag_1464_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*14 + 1, v_suppressElabErrors_1466_);
v___x_1476_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; size_t v_sz_1478_; size_t v___x_1479_; lean_object* v___x_1480_; lean_object* v_msg_1481_; lean_object* v___x_1482_; lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1520_; 
v___x_1477_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1473_);
lean_dec_ref(v_traces_1473_);
v_sz_1478_ = lean_array_size(v___x_1477_);
v___x_1479_ = ((size_t)0ULL);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21(v_sz_1478_, v___x_1479_, v___x_1477_);
v_msg_1481_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1481_, 0, v_data_1444_);
lean_ctor_set(v_msg_1481_, 1, v_msg_1446_);
lean_ctor_set(v_msg_1481_, 2, v___x_1480_);
v___x_1482_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4(v_msg_1481_, v___y_1447_, v___y_1448_, v___x_1476_, v___y_1450_);
lean_dec_ref(v___x_1476_);
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1520_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1520_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v_traceState_1488_; lean_object* v_env_1489_; lean_object* v_nextMacroScope_1490_; lean_object* v_ngen_1491_; lean_object* v_auxDeclNGen_1492_; lean_object* v_cache_1493_; lean_object* v_messages_1494_; lean_object* v_infoState_1495_; lean_object* v_snapshotTasks_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1519_; 
v___x_1487_ = lean_st_ref_take(v___y_1450_);
v_traceState_1488_ = lean_ctor_get(v___x_1487_, 4);
v_env_1489_ = lean_ctor_get(v___x_1487_, 0);
v_nextMacroScope_1490_ = lean_ctor_get(v___x_1487_, 1);
v_ngen_1491_ = lean_ctor_get(v___x_1487_, 2);
v_auxDeclNGen_1492_ = lean_ctor_get(v___x_1487_, 3);
v_cache_1493_ = lean_ctor_get(v___x_1487_, 5);
v_messages_1494_ = lean_ctor_get(v___x_1487_, 6);
v_infoState_1495_ = lean_ctor_get(v___x_1487_, 7);
v_snapshotTasks_1496_ = lean_ctor_get(v___x_1487_, 8);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1498_ = v___x_1487_;
v_isShared_1499_ = v_isSharedCheck_1519_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snapshotTasks_1496_);
lean_inc(v_infoState_1495_);
lean_inc(v_messages_1494_);
lean_inc(v_cache_1493_);
lean_inc(v_traceState_1488_);
lean_inc(v_auxDeclNGen_1492_);
lean_inc(v_ngen_1491_);
lean_inc(v_nextMacroScope_1490_);
lean_inc(v_env_1489_);
lean_dec(v___x_1487_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1519_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint64_t v_tid_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1517_; 
v_tid_1500_ = lean_ctor_get_uint64(v_traceState_1488_, sizeof(void*)*1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_traceState_1488_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_traceState_1488_, 0);
lean_dec(v_unused_1518_);
v___x_1502_ = v_traceState_1488_;
v_isShared_1503_ = v_isSharedCheck_1517_;
goto v_resetjp_1501_;
}
else
{
lean_dec(v_traceState_1488_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1517_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v_ref_1445_);
lean_ctor_set(v___x_1504_, 1, v_a_1483_);
v___x_1505_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1443_, v___x_1504_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1505_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1505_);
lean_ctor_set_uint64(v_reuseFailAlloc_1516_, sizeof(void*)*1, v_tid_1500_);
v___x_1507_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 4, v___x_1507_);
v___x_1509_ = v___x_1498_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_env_1489_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_nextMacroScope_1490_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_ngen_1491_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_auxDeclNGen_1492_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1515_, 5, v_cache_1493_);
lean_ctor_set(v_reuseFailAlloc_1515_, 6, v_messages_1494_);
lean_ctor_set(v_reuseFailAlloc_1515_, 7, v_infoState_1495_);
lean_ctor_set(v_reuseFailAlloc_1515_, 8, v_snapshotTasks_1496_);
v___x_1509_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1510_ = lean_st_ref_set(v___y_1450_, v___x_1509_);
v___x_1511_ = lean_box(0);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1511_);
v___x_1513_ = v___x_1485_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19___boxed(lean_object* v_oldTraces_1523_, lean_object* v_data_1524_, lean_object* v_ref_1525_, lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19(v_oldTraces_1523_, v_data_1524_, v_ref_1525_, v_msg_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(lean_object* v_x_1533_){
_start:
{
if (lean_obj_tag(v_x_1533_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v_x_1533_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v_x_1533_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v_x_1533_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 1);
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v_x_1533_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v_x_1533_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v_x_1533_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 0);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg___boxed(lean_object* v_x_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(v_x_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(lean_object* v_opts_1554_, lean_object* v_opt_1555_){
_start:
{
lean_object* v_name_1556_; lean_object* v_defValue_1557_; lean_object* v_map_1558_; lean_object* v___x_1559_; 
v_name_1556_ = lean_ctor_get(v_opt_1555_, 0);
v_defValue_1557_ = lean_ctor_get(v_opt_1555_, 1);
v_map_1558_ = lean_ctor_get(v_opts_1554_, 0);
v___x_1559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1558_, v_name_1556_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_inc(v_defValue_1557_);
return v_defValue_1557_;
}
else
{
lean_object* v_val_1560_; 
v_val_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_val_1560_);
lean_dec_ref(v___x_1559_);
if (lean_obj_tag(v_val_1560_) == 3)
{
lean_object* v_v_1561_; 
v_v_1561_ = lean_ctor_get(v_val_1560_, 0);
lean_inc(v_v_1561_);
lean_dec_ref(v_val_1560_);
return v_v_1561_;
}
else
{
lean_dec(v_val_1560_);
lean_inc(v_defValue_1557_);
return v_defValue_1557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21___boxed(lean_object* v_opts_1562_, lean_object* v_opt_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(v_opts_1562_, v_opt_1563_);
lean_dec_ref(v_opt_1563_);
lean_dec_ref(v_opts_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18(lean_object* v_e_1565_){
_start:
{
if (lean_obj_tag(v_e_1565_) == 0)
{
uint8_t v___x_1566_; 
v___x_1566_ = 2;
return v___x_1566_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = 0;
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18___boxed(lean_object* v_e_1568_){
_start:
{
uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_res_1569_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18(v_e_1568_);
lean_dec_ref(v_e_1568_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__0));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__2));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4(void){
_start:
{
lean_object* v___x_1577_; double v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(1000u);
v___x_1578_ = lean_float_of_nat(v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(lean_object* v_cls_1579_, uint8_t v_collapsed_1580_, lean_object* v_tag_1581_, lean_object* v_opts_1582_, uint8_t v_clsEnabled_1583_, lean_object* v_oldTraces_1584_, lean_object* v_msg_1585_, lean_object* v_resStartStop_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_fst_1592_; lean_object* v_snd_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1691_; 
v_fst_1592_ = lean_ctor_get(v_resStartStop_1586_, 0);
v_snd_1593_ = lean_ctor_get(v_resStartStop_1586_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_resStartStop_1586_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1595_ = v_resStartStop_1586_;
v_isShared_1596_ = v_isSharedCheck_1691_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_snd_1593_);
lean_inc(v_fst_1592_);
lean_dec(v_resStartStop_1586_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1691_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v_data_1600_; lean_object* v_fst_1611_; lean_object* v_snd_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1690_; 
v_fst_1611_ = lean_ctor_get(v_snd_1593_, 0);
v_snd_1612_ = lean_ctor_get(v_snd_1593_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_snd_1593_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1614_ = v_snd_1593_;
v_isShared_1615_ = v_isSharedCheck_1690_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_snd_1612_);
lean_inc(v_fst_1611_);
lean_dec(v_snd_1593_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1690_;
goto v_resetjp_1613_;
}
v___jp_1597_:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19(v_oldTraces_1584_, v_data_1600_, v___y_1598_, v___y_1599_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; 
lean_dec_ref(v___x_1601_);
v___x_1602_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(v_fst_1592_);
return v___x_1602_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_fst_1592_);
v_a_1603_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1601_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1601_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___y_1619_; lean_object* v_a_1620_; uint8_t v___y_1644_; double v___y_1675_; 
v___x_1616_ = l_Lean_trace_profiler;
v___x_1617_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_opts_1582_, v___x_1616_);
if (v___x_1617_ == 0)
{
v___y_1644_ = v___x_1617_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1681_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_opts_1582_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; double v___x_1684_; double v___x_1685_; double v___x_1686_; 
v___x_1682_ = l_Lean_trace_profiler_threshold;
v___x_1683_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(v_opts_1582_, v___x_1682_);
v___x_1684_ = lean_float_of_nat(v___x_1683_);
v___x_1685_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4);
v___x_1686_ = lean_float_div(v___x_1684_, v___x_1685_);
v___y_1675_ = v___x_1686_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; double v___x_1689_; 
v___x_1687_ = l_Lean_trace_profiler_threshold;
v___x_1688_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(v_opts_1582_, v___x_1687_);
v___x_1689_ = lean_float_of_nat(v___x_1688_);
v___y_1675_ = v___x_1689_;
goto v___jp_1674_;
}
}
v___jp_1618_:
{
uint8_t v_result_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v_result_1621_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18(v_fst_1592_);
v___x_1622_ = l_Lean_TraceResult_toEmoji(v_result_1621_);
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
v___x_1624_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1);
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 7);
lean_ctor_set(v___x_1614_, 1, v___x_1624_);
lean_ctor_set(v___x_1614_, 0, v___x_1623_);
v___x_1626_ = v___x_1614_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v_m_1628_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 7);
lean_ctor_set(v___x_1595_, 1, v_a_1620_);
lean_ctor_set(v___x_1595_, 0, v___x_1626_);
v_m_1628_ = v___x_1595_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_a_1620_);
v_m_1628_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; double v___x_1631_; lean_object* v_data_1632_; 
v___x_1629_ = lean_box(v_result_1621_);
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
v___x_1631_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0);
lean_inc_ref(v_tag_1581_);
lean_inc_ref(v___x_1630_);
lean_inc(v_cls_1579_);
v_data_1632_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1632_, 0, v_cls_1579_);
lean_ctor_set(v_data_1632_, 1, v___x_1630_);
lean_ctor_set(v_data_1632_, 2, v_tag_1581_);
lean_ctor_set_float(v_data_1632_, sizeof(void*)*3, v___x_1631_);
lean_ctor_set_float(v_data_1632_, sizeof(void*)*3 + 8, v___x_1631_);
lean_ctor_set_uint8(v_data_1632_, sizeof(void*)*3 + 16, v_collapsed_1580_);
if (v___x_1617_ == 0)
{
lean_dec_ref(v___x_1630_);
lean_dec(v_snd_1612_);
lean_dec(v_fst_1611_);
lean_dec_ref(v_tag_1581_);
lean_dec(v_cls_1579_);
v___y_1598_ = v___y_1619_;
v___y_1599_ = v_m_1628_;
v_data_1600_ = v_data_1632_;
goto v___jp_1597_;
}
else
{
lean_object* v_data_1633_; double v___x_1634_; double v___x_1635_; 
lean_dec_ref(v_data_1632_);
v_data_1633_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1633_, 0, v_cls_1579_);
lean_ctor_set(v_data_1633_, 1, v___x_1630_);
lean_ctor_set(v_data_1633_, 2, v_tag_1581_);
v___x_1634_ = lean_unbox_float(v_fst_1611_);
lean_dec(v_fst_1611_);
lean_ctor_set_float(v_data_1633_, sizeof(void*)*3, v___x_1634_);
v___x_1635_ = lean_unbox_float(v_snd_1612_);
lean_dec(v_snd_1612_);
lean_ctor_set_float(v_data_1633_, sizeof(void*)*3 + 8, v___x_1635_);
lean_ctor_set_uint8(v_data_1633_, sizeof(void*)*3 + 16, v_collapsed_1580_);
v___y_1598_ = v___y_1619_;
v___y_1599_ = v_m_1628_;
v_data_1600_ = v_data_1633_;
goto v___jp_1597_;
}
}
}
}
v___jp_1638_:
{
lean_object* v_ref_1639_; lean_object* v___x_1640_; 
v_ref_1639_ = lean_ctor_get(v___y_1589_, 5);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v_fst_1592_);
v___x_1640_ = lean_apply_6(v_msg_1585_, v_fst_1592_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, lean_box(0));
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1640_);
lean_inc(v_ref_1639_);
v___y_1619_ = v_ref_1639_;
v_a_1620_ = v_a_1641_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1642_; 
lean_dec_ref(v___x_1640_);
v___x_1642_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3);
lean_inc(v_ref_1639_);
v___y_1619_ = v_ref_1639_;
v_a_1620_ = v___x_1642_;
goto v___jp_1618_;
}
}
v___jp_1643_:
{
if (v_clsEnabled_1583_ == 0)
{
if (v___y_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v_traceState_1646_; lean_object* v_env_1647_; lean_object* v_nextMacroScope_1648_; lean_object* v_ngen_1649_; lean_object* v_auxDeclNGen_1650_; lean_object* v_cache_1651_; lean_object* v_messages_1652_; lean_object* v_infoState_1653_; lean_object* v_snapshotTasks_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1673_; 
lean_del_object(v___x_1614_);
lean_dec(v_snd_1612_);
lean_dec(v_fst_1611_);
lean_del_object(v___x_1595_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec_ref(v_msg_1585_);
lean_dec_ref(v_tag_1581_);
lean_dec(v_cls_1579_);
v___x_1645_ = lean_st_ref_take(v___y_1590_);
v_traceState_1646_ = lean_ctor_get(v___x_1645_, 4);
v_env_1647_ = lean_ctor_get(v___x_1645_, 0);
v_nextMacroScope_1648_ = lean_ctor_get(v___x_1645_, 1);
v_ngen_1649_ = lean_ctor_get(v___x_1645_, 2);
v_auxDeclNGen_1650_ = lean_ctor_get(v___x_1645_, 3);
v_cache_1651_ = lean_ctor_get(v___x_1645_, 5);
v_messages_1652_ = lean_ctor_get(v___x_1645_, 6);
v_infoState_1653_ = lean_ctor_get(v___x_1645_, 7);
v_snapshotTasks_1654_ = lean_ctor_get(v___x_1645_, 8);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1656_ = v___x_1645_;
v_isShared_1657_ = v_isSharedCheck_1673_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_snapshotTasks_1654_);
lean_inc(v_infoState_1653_);
lean_inc(v_messages_1652_);
lean_inc(v_cache_1651_);
lean_inc(v_traceState_1646_);
lean_inc(v_auxDeclNGen_1650_);
lean_inc(v_ngen_1649_);
lean_inc(v_nextMacroScope_1648_);
lean_inc(v_env_1647_);
lean_dec(v___x_1645_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1673_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
uint64_t v_tid_1658_; lean_object* v_traces_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1672_; 
v_tid_1658_ = lean_ctor_get_uint64(v_traceState_1646_, sizeof(void*)*1);
v_traces_1659_ = lean_ctor_get(v_traceState_1646_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_traceState_1646_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1661_ = v_traceState_1646_;
v_isShared_1662_ = v_isSharedCheck_1672_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_traces_1659_);
lean_dec(v_traceState_1646_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1672_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1584_, v_traces_1659_);
lean_dec_ref(v_traces_1659_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1663_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1663_);
lean_ctor_set_uint64(v_reuseFailAlloc_1671_, sizeof(void*)*1, v_tid_1658_);
v___x_1665_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 4, v___x_1665_);
v___x_1667_ = v___x_1656_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_env_1647_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_nextMacroScope_1648_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_ngen_1649_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_auxDeclNGen_1650_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1670_, 5, v_cache_1651_);
lean_ctor_set(v_reuseFailAlloc_1670_, 6, v_messages_1652_);
lean_ctor_set(v_reuseFailAlloc_1670_, 7, v_infoState_1653_);
lean_ctor_set(v_reuseFailAlloc_1670_, 8, v_snapshotTasks_1654_);
v___x_1667_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_st_ref_set(v___y_1590_, v___x_1667_);
lean_dec(v___y_1590_);
v___x_1669_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(v_fst_1592_);
return v___x_1669_;
}
}
}
}
}
else
{
goto v___jp_1638_;
}
}
else
{
goto v___jp_1638_;
}
}
v___jp_1674_:
{
double v___x_1676_; double v___x_1677_; double v___x_1678_; uint8_t v___x_1679_; 
v___x_1676_ = lean_unbox_float(v_snd_1612_);
v___x_1677_ = lean_unbox_float(v_fst_1611_);
v___x_1678_ = lean_float_sub(v___x_1676_, v___x_1677_);
v___x_1679_ = lean_float_decLt(v___y_1675_, v___x_1678_);
v___y_1644_ = v___x_1679_;
goto v___jp_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___boxed(lean_object* v_cls_1692_, lean_object* v_collapsed_1693_, lean_object* v_tag_1694_, lean_object* v_opts_1695_, lean_object* v_clsEnabled_1696_, lean_object* v_oldTraces_1697_, lean_object* v_msg_1698_, lean_object* v_resStartStop_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v_collapsed_boxed_1705_; uint8_t v_clsEnabled_boxed_1706_; lean_object* v_res_1707_; 
v_collapsed_boxed_1705_ = lean_unbox(v_collapsed_1693_);
v_clsEnabled_boxed_1706_ = lean_unbox(v_clsEnabled_1696_);
v_res_1707_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(v_cls_1692_, v_collapsed_boxed_1705_, v_tag_1694_, v_opts_1695_, v_clsEnabled_boxed_1706_, v_oldTraces_1697_, v_msg_1698_, v_resStartStop_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec_ref(v_opts_1695_);
return v_res_1707_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__2));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__0));
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
return v___x_1716_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__2));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__4));
v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
return v___x_1722_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__6));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__8));
v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(lean_object* v_upperBound_1729_, lean_object* v_fst_1730_, lean_object* v_args_1731_, uint8_t v_compile_1732_, uint8_t v_logCompileErrors_1733_, uint8_t v___x_1734_, lean_object* v_a_1735_, lean_object* v_b_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_a_1743_; lean_object* v___y_1748_; uint8_t v___x_1767_; 
v___x_1767_ = lean_nat_dec_lt(v_a_1735_, v_upperBound_1729_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_b_1736_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_array_fget_borrowed(v_fst_1730_, v_a_1735_);
v___x_1770_ = l_Lean_Expr_mvarId_x21(v___x_1769_);
lean_inc(v___x_1770_);
v___x_1771_ = l_Lean_MVarId_getDecl(v___x_1770_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v_type_1773_; lean_object* v___x_1774_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v___x_1771_);
v_type_1773_ = lean_ctor_get(v_a_1772_, 2);
lean_inc_ref(v_type_1773_);
lean_dec(v_a_1772_);
v___x_1774_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_1773_, v___y_1738_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v_a_1775_);
v___x_1776_ = l_Lean_Meta_isProp(v_a_1775_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; lean_object* v_cls_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = lean_box(0);
v_cls_1779_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_1780_ = lean_array_fget_borrowed(v_args_1731_, v_a_1735_);
v___x_1781_ = lean_unbox(v_a_1777_);
lean_dec(v_a_1777_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v_a_1775_);
v___x_1782_ = l_Lean_Meta_isClass_x3f(v_a_1775_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1883_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1883_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1883_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
if (lean_obj_tag(v_a_1783_) == 0)
{
lean_object* v_options_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
lean_del_object(v___x_1785_);
v_options_1787_ = lean_ctor_get(v___y_1739_, 2);
v___x_1788_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_1789_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; 
lean_dec(v_a_1775_);
lean_inc(v___x_1780_);
v___x_1790_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1770_, v___x_1780_, v___y_1738_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_dec_ref(v___x_1790_);
v_a_1743_ = v___x_1778_;
goto v___jp_1742_;
}
else
{
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
return v___x_1790_;
}
}
else
{
lean_object* v___x_1791_; 
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___x_1780_);
v___x_1791_ = lean_infer_type(v___x_1780_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1793_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v_a_1775_);
v___x_1793_ = l_Lean_Meta_isExprDefEq(v_a_1775_, v_a_1792_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; uint8_t v___x_1795_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = lean_unbox(v_a_1794_);
lean_dec(v_a_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1));
v___x_1797_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_1796_, v___y_1740_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v___x_1797_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___x_1780_);
lean_inc(v_a_1798_);
v___x_1799_ = l_Lean_Meta_mkAuxDefinition(v_a_1798_, v_a_1775_, v___x_1780_, v___x_1734_, v___x_1734_, v___x_1767_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1770_, v_a_1800_, v___y_1738_);
if (lean_obj_tag(v___x_1801_) == 0)
{
uint8_t v___x_1802_; lean_object* v___x_1803_; 
lean_dec_ref(v___x_1801_);
v___x_1802_ = 0;
lean_inc(v_a_1798_);
v___x_1803_ = l_Lean_Meta_setInlineAttribute(v_a_1798_, v___x_1802_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_dec_ref(v___x_1803_);
if (v_compile_1732_ == 0)
{
lean_object* v___x_1804_; 
lean_inc_ref(v___y_1739_);
v___x_1804_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_1798_, v___x_1778_, v___x_1778_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
v___y_1748_ = v___x_1804_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_unsigned_to_nat(1u);
v___x_1806_ = lean_mk_empty_array_with_capacity(v___x_1805_);
lean_inc(v_a_1798_);
v___x_1807_ = lean_array_push(v___x_1806_, v_a_1798_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
v___x_1808_ = l_Lean_compileDecls(v___x_1807_, v_logCompileErrors_1733_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
lean_inc_ref(v___y_1739_);
v___x_1810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_1798_, v___x_1778_, v_a_1809_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
v___y_1748_ = v___x_1810_;
goto v___jp_1747_;
}
else
{
lean_dec(v_a_1798_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
return v___x_1808_;
}
}
}
else
{
lean_dec(v_a_1798_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
return v___x_1803_;
}
}
else
{
lean_dec(v_a_1798_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
return v___x_1801_;
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_a_1798_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1811_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1799_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1799_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1819_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1797_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1797_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_object* v___x_1827_; 
lean_dec(v_a_1775_);
lean_inc(v___x_1780_);
v___x_1827_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1770_, v___x_1780_, v___y_1738_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_dec_ref(v___x_1827_);
v_a_1743_ = v___x_1778_;
goto v___jp_1742_;
}
else
{
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
return v___x_1827_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1828_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1793_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1793_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1836_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1791_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1791_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
else
{
lean_object* v_options_1844_; lean_object* v_a_1846_; lean_object* v___y_1849_; uint8_t v___y_1850_; lean_object* v_a_1855_; lean_object* v___y_1859_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
lean_dec_ref(v_a_1783_);
v_options_1844_ = lean_ctor_get(v___y_1739_, 2);
v___x_1863_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_1864_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_1844_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_del_object(v___x_1785_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___x_1780_);
v___x_1865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_1780_, v_a_1775_, v_compile_1732_, v_logCompileErrors_1733_, v___x_1770_, v___x_1778_, v___x_1778_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
v___y_1748_ = v___x_1865_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_box(0);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v_a_1775_);
v___x_1867_ = l_Lean_Meta_trySynthInstance(v_a_1775_, v___x_1866_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1867_);
if (lean_obj_tag(v_a_1868_) == 1)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_ctor_get(v_a_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v_a_1868_);
v___x_1870_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_1779_, v___y_1739_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; uint8_t v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = lean_unbox(v_a_1871_);
lean_dec(v_a_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_inc(v___x_1770_);
v___x_1873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_1770_, v_a_1869_, v___x_1778_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
v___y_1859_ = v___x_1873_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1874_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1);
lean_inc(v_a_1869_);
v___x_1875_ = l_Lean_MessageData_ofExpr(v_a_1869_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_1779_, v___x_1876_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
lean_inc(v___x_1770_);
v___x_1879_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_1770_, v_a_1869_, v_a_1878_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
v___y_1859_ = v___x_1879_;
goto v___jp_1858_;
}
else
{
lean_object* v_a_1880_; 
lean_dec(v_a_1869_);
v_a_1880_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1877_);
v_a_1855_ = v_a_1880_;
goto v___jp_1854_;
}
}
}
else
{
lean_object* v_a_1881_; 
lean_dec(v_a_1869_);
v_a_1881_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1870_);
v_a_1855_ = v_a_1881_;
goto v___jp_1854_;
}
}
else
{
lean_dec(v_a_1868_);
lean_del_object(v___x_1785_);
v_a_1846_ = v___x_1778_;
goto v___jp_1845_;
}
}
else
{
lean_object* v_a_1882_; 
v_a_1882_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1867_);
v_a_1855_ = v_a_1882_;
goto v___jp_1854_;
}
}
v___jp_1845_:
{
lean_object* v___x_1847_; 
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___x_1780_);
v___x_1847_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_1780_, v_a_1775_, v_compile_1732_, v_logCompileErrors_1733_, v___x_1770_, v___x_1778_, v_a_1846_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
v___y_1748_ = v___x_1847_;
goto v___jp_1747_;
}
v___jp_1848_:
{
if (v___y_1850_ == 0)
{
lean_dec_ref(v___y_1849_);
lean_del_object(v___x_1785_);
v_a_1846_ = v___x_1778_;
goto v___jp_1845_;
}
else
{
lean_object* v___x_1852_; 
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 1);
lean_ctor_set(v___x_1785_, 0, v___y_1849_);
v___x_1852_ = v___x_1785_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___y_1849_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
v___jp_1854_:
{
uint8_t v___x_1856_; 
v___x_1856_ = l_Lean_Exception_isInterrupt(v_a_1855_);
if (v___x_1856_ == 0)
{
uint8_t v___x_1857_; 
lean_inc_ref(v_a_1855_);
v___x_1857_ = l_Lean_Exception_isRuntime(v_a_1855_);
v___y_1849_ = v_a_1855_;
v___y_1850_ = v___x_1857_;
goto v___jp_1848_;
}
else
{
v___y_1849_ = v_a_1855_;
v___y_1850_ = v___x_1856_;
goto v___jp_1848_;
}
}
v___jp_1858_:
{
if (lean_obj_tag(v___y_1859_) == 0)
{
lean_object* v_a_1860_; 
lean_del_object(v___x_1785_);
v_a_1860_ = lean_ctor_get(v___y_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___y_1859_);
if (lean_obj_tag(v_a_1860_) == 0)
{
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
v_a_1743_ = v___x_1778_;
goto v___jp_1742_;
}
else
{
lean_object* v_a_1861_; 
v_a_1861_ = lean_ctor_get(v_a_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref(v_a_1860_);
v_a_1846_ = v_a_1861_;
goto v___jp_1845_;
}
}
else
{
lean_object* v_a_1862_; 
v_a_1862_ = lean_ctor_get(v___y_1859_, 0);
lean_inc(v_a_1862_);
lean_dec_ref(v___y_1859_);
v_a_1855_ = v_a_1862_;
goto v___jp_1854_;
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1884_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1782_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1782_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_1892_; 
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___x_1780_);
v___x_1892_ = lean_infer_type(v___x_1780_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v_a_1893_);
lean_inc(v_a_1775_);
v___x_1894_ = l_Lean_Meta_isExprDefEq(v_a_1775_, v_a_1893_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; uint8_t v___x_1896_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1894_);
v___x_1896_ = lean_unbox(v_a_1895_);
lean_dec(v_a_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_1779_, v___y_1739_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; uint8_t v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = lean_unbox(v_a_1898_);
lean_dec(v_a_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; 
lean_dec(v_a_1893_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___x_1780_);
v___x_1900_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_1775_, v___x_1780_, v___x_1767_, v___x_1770_, v___x_1778_, v___x_1778_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
v___y_1748_ = v___x_1900_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1901_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3);
lean_inc(v_a_1735_);
v___x_1902_ = l_Nat_reprFast(v_a_1735_);
v___x_1903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
v___x_1904_ = l_Lean_MessageData_ofFormat(v___x_1903_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1901_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
lean_inc(v_a_1775_);
v___x_1908_ = l_Lean_MessageData_ofExpr(v_a_1775_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_MessageData_ofExpr(v_a_1893_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
lean_inc(v___x_1780_);
v___x_1916_ = l_Lean_MessageData_ofExpr(v___x_1780_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_1779_, v___x_1917_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___x_1780_);
v___x_1920_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_1775_, v___x_1780_, v___x_1767_, v___x_1770_, v___x_1778_, v_a_1919_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
v___y_1748_ = v___x_1920_;
goto v___jp_1747_;
}
else
{
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
return v___x_1918_;
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_a_1893_);
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1921_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1897_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1897_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v___x_1929_; 
lean_dec(v_a_1893_);
lean_dec(v_a_1775_);
lean_inc(v___x_1780_);
v___x_1929_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1770_, v___x_1780_, v___y_1738_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_dec_ref(v___x_1929_);
v_a_1743_ = v___x_1778_;
goto v___jp_1742_;
}
else
{
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
return v___x_1929_;
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_a_1893_);
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1930_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1894_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1894_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1938_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1892_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1892_);
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
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_a_1775_);
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1946_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1776_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1776_);
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
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1954_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1774_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1774_);
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
lean_dec(v___x_1770_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1962_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1771_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1771_);
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
v___jp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v_a_1735_, v___x_1744_);
lean_dec(v_a_1735_);
v_a_1735_ = v___x_1745_;
v_b_1736_ = v_a_1743_;
goto _start;
}
v___jp_1747_:
{
if (lean_obj_tag(v___y_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1758_; 
v_a_1749_ = lean_ctor_get(v___y_1748_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___y_1748_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1751_ = v___y_1748_;
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___y_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
if (lean_obj_tag(v_a_1749_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; 
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1753_ = lean_ctor_get(v_a_1749_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v_a_1749_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v_a_1753_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
else
{
lean_object* v_a_1757_; 
lean_del_object(v___x_1751_);
v_a_1757_ = lean_ctor_get(v_a_1749_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v_a_1749_);
v_a_1743_ = v_a_1757_;
goto v___jp_1742_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_a_1735_);
v_a_1759_ = lean_ctor_get(v___y_1748_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___y_1748_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___y_1748_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___y_1748_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__4));
v___x_1972_ = l_Lean_stringToMessageData(v___x_1971_);
return v___x_1972_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__6));
v___x_1975_ = l_Lean_stringToMessageData(v___x_1974_);
return v___x_1975_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__8));
v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__10));
v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10(lean_object* v_a_1982_, lean_object* v_expectedType_1983_, uint8_t v___x_1984_, uint8_t v_compile_1985_, uint8_t v_logCompileErrors_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; 
if (lean_obj_tag(v_x_1987_) == 5)
{
lean_object* v_fn_2048_; lean_object* v_arg_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_fn_2048_ = lean_ctor_get(v_x_1987_, 0);
lean_inc_ref(v_fn_2048_);
v_arg_2049_ = lean_ctor_get(v_x_1987_, 1);
lean_inc_ref(v_arg_2049_);
lean_dec_ref(v_x_1987_);
v___x_2050_ = lean_array_set(v_x_1988_, v_x_1989_, v_arg_2049_);
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = lean_nat_sub(v_x_1989_, v___x_2051_);
lean_dec(v_x_1989_);
v_x_1987_ = v_fn_2048_;
v_x_1988_ = v___x_2050_;
v_x_1989_ = v___x_2052_;
goto _start;
}
else
{
lean_object* v_cls_2054_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___x_2075_; 
lean_dec(v_x_1989_);
v_cls_2054_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_2075_ = l_Lean_Expr_constName_x3f(v_x_1987_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
v___y_2056_ = v___y_1990_;
v___y_2057_ = v___y_1991_;
v___y_2058_ = v___y_1992_;
v___y_2059_ = v___y_1993_;
goto v___jp_2055_;
}
else
{
lean_object* v_val_2076_; lean_object* v___x_2077_; 
v_val_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref(v___x_2075_);
lean_inc_ref(v___y_1992_);
v___x_2077_ = l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(v_val_2076_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2077_);
if (lean_obj_tag(v_a_2078_) == 6)
{
lean_object* v_val_2079_; lean_object* v___x_2080_; 
lean_dec_ref(v_a_1982_);
v_val_2079_ = lean_ctor_get(v_a_2078_, 0);
lean_inc_ref(v_val_2079_);
lean_dec_ref(v_a_2078_);
lean_inc(v___y_1993_);
lean_inc_ref(v___y_1992_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc_ref(v_x_1987_);
v___x_2080_ = lean_infer_type(v_x_1987_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = 0;
lean_inc(v___y_1993_);
lean_inc_ref(v___y_1992_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
v___x_2083_ = l_Lean_Meta_forallMetaTelescope(v_a_2081_, v___x_2082_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v_snd_2085_; lean_object* v_fst_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2185_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2083_);
v_snd_2085_ = lean_ctor_get(v_a_2084_, 1);
v_fst_2086_ = lean_ctor_get(v_a_2084_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_a_2084_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2088_ = v_a_2084_;
v_isShared_2089_ = v_isSharedCheck_2185_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_snd_2085_);
lean_inc(v_fst_2086_);
lean_dec(v_a_2084_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2185_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_snd_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2183_; 
v_snd_2090_ = lean_ctor_get(v_snd_2085_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_snd_2085_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v_snd_2085_, 0);
lean_dec(v_unused_2184_);
v___x_2092_ = v_snd_2085_;
v_isShared_2093_ = v_isSharedCheck_2183_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_snd_2090_);
lean_dec(v_snd_2085_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2183_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2094_ = lean_array_get_size(v_x_1988_);
v___x_2131_ = lean_array_get_size(v_fst_2086_);
v___x_2132_ = lean_nat_dec_eq(v___x_2094_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
lean_dec(v_snd_2090_);
lean_dec(v_fst_2086_);
lean_dec_ref(v_val_2079_);
lean_dec_ref(v_expectedType_1983_);
v___x_2133_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5);
v___x_2134_ = l_Lean_MessageData_ofExpr(v_x_1987_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 7);
lean_ctor_set(v___x_2092_, 1, v___x_2134_);
lean_ctor_set(v___x_2092_, 0, v___x_2133_);
v___x_2136_ = v___x_2092_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7);
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 7);
lean_ctor_set(v___x_2088_, 1, v___x_2137_);
lean_ctor_set(v___x_2088_, 0, v___x_2136_);
v___x_2139_ = v___x_2088_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2140_ = lean_array_to_list(v_x_1988_);
v___x_2141_ = lean_box(0);
v___x_2142_ = l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(v___x_2140_, v___x_2141_);
v___x_2143_ = l_Lean_MessageData_ofList(v___x_2142_);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2139_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_2144_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
return v___x_2145_;
}
}
}
else
{
lean_object* v___x_2148_; 
lean_inc(v___y_1993_);
lean_inc_ref(v___y_1992_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc_ref(v_expectedType_1983_);
v___x_2148_ = l_Lean_Meta_isExprDefEq(v_expectedType_1983_, v_snd_2090_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; uint8_t v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = lean_unbox(v_a_2149_);
lean_dec(v_a_2149_);
if (v___x_2150_ == 0)
{
lean_object* v_toConstantVal_2151_; lean_object* v_name_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
lean_dec(v_fst_2086_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
v_toConstantVal_2151_ = lean_ctor_get(v_val_2079_, 0);
lean_inc_ref(v_toConstantVal_2151_);
lean_dec_ref(v_val_2079_);
v_name_2152_ = lean_ctor_get(v_toConstantVal_2151_, 0);
lean_inc(v_name_2152_);
lean_dec_ref(v_toConstantVal_2151_);
v___x_2153_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9);
v___x_2154_ = l_Lean_MessageData_ofExpr(v_expectedType_1983_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 7);
lean_ctor_set(v___x_2092_, 1, v___x_2154_);
lean_ctor_set(v___x_2092_, 0, v___x_2153_);
v___x_2156_ = v___x_2092_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11);
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 7);
lean_ctor_set(v___x_2088_, 1, v___x_2157_);
lean_ctor_set(v___x_2088_, 0, v___x_2156_);
v___x_2159_ = v___x_2088_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v___x_2160_ = l_Lean_MessageData_ofConstName(v_name_2152_, v___x_1984_);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_2163_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
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
}
else
{
lean_del_object(v___x_2092_);
lean_del_object(v___x_2088_);
lean_dec_ref(v_expectedType_1983_);
v___y_2096_ = v___y_1990_;
v___y_2097_ = v___y_1991_;
v___y_2098_ = v___y_1992_;
v___y_2099_ = v___y_1993_;
goto v___jp_2095_;
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_del_object(v___x_2092_);
lean_del_object(v___x_2088_);
lean_dec(v_fst_2086_);
lean_dec_ref(v_val_2079_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_expectedType_1983_);
v_a_2175_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2148_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2148_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
v___jp_2095_:
{
lean_object* v_numParams_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_numParams_2100_ = lean_ctor_get(v_val_2079_, 3);
lean_inc(v_numParams_2100_);
lean_dec_ref(v_val_2079_);
v___x_2101_ = lean_box(0);
lean_inc(v___y_2097_);
v___x_2102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(v___x_2094_, v_fst_2086_, v_x_1988_, v_compile_1985_, v_logCompileErrors_1986_, v___x_1984_, v_numParams_2100_, v___x_2101_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec_ref(v_x_1988_);
if (lean_obj_tag(v___x_2102_) == 0)
{
size_t v_sz_2103_; size_t v___x_2104_; lean_object* v___x_2105_; 
lean_dec_ref(v___x_2102_);
v_sz_2103_ = lean_array_size(v_fst_2086_);
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_2103_, v___x_2104_, v_fst_2086_, v___y_2097_);
lean_dec(v___y_2097_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2114_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = l_Lean_mkAppN(v_x_1987_, v_a_2106_);
lean_dec(v_a_2106_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2110_);
v___x_2112_ = v___x_2108_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_x_1987_);
v_a_2115_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2105_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2105_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v___y_2097_);
lean_dec(v_fst_2086_);
lean_dec_ref(v_x_1987_);
v_a_2123_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2102_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2102_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_val_2079_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_expectedType_1983_);
v_a_2186_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2083_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2083_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_dec_ref(v_val_2079_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_expectedType_1983_);
return v___x_2080_;
}
}
else
{
lean_dec(v_a_2078_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
v___y_2056_ = v___y_1990_;
v___y_2057_ = v___y_1991_;
v___y_2058_ = v___y_1992_;
v___y_2059_ = v___y_1993_;
goto v___jp_2055_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_expectedType_1983_);
lean_dec_ref(v_a_1982_);
v_a_2194_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2077_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2077_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
v___jp_2055_:
{
lean_object* v___x_2060_; lean_object* v_a_2061_; uint8_t v___x_2062_; 
v___x_2060_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2054_, v___y_2058_);
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2060_);
v___x_2062_ = lean_unbox(v_a_2061_);
lean_dec(v_a_2061_);
if (v___x_2062_ == 0)
{
v___y_1996_ = v___y_2056_;
v___y_1997_ = v___y_2057_;
v___y_1998_ = v___y_2058_;
v___y_1999_ = v___y_2059_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2063_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3);
lean_inc_ref(v_a_1982_);
v___x_2064_ = l_Lean_MessageData_ofExpr(v_a_1982_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2054_, v___x_2065_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_dec_ref(v___x_2066_);
v___y_1996_ = v___y_2056_;
v___y_1997_ = v___y_2057_;
v___y_1998_ = v___y_2058_;
v___y_1999_ = v___y_2059_;
goto v___jp_1995_;
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec_ref(v_expectedType_1983_);
lean_dec_ref(v_a_1982_);
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
v___jp_1995_:
{
lean_object* v_options_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_options_2000_ = lean_ctor_get(v___y_1998_, 2);
v___x_2001_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2002_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2000_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_expectedType_1983_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_a_1982_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; 
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
lean_inc_ref(v_a_1982_);
v___x_2004_ = lean_infer_type(v_a_1982_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
lean_inc_ref(v_expectedType_1983_);
v___x_2006_ = l_Lean_Meta_isExprDefEq(v_expectedType_1983_, v_a_2005_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2039_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2039_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2039_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_unbox(v_a_2007_);
lean_dec(v_a_2007_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v_a_2014_; lean_object* v___x_2015_; 
lean_del_object(v___x_2009_);
v___x_2012_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1));
v___x_2013_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2012_, v___y_1999_);
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc(v_a_2014_);
v___x_2015_ = l_Lean_Meta_mkAuxDefinition(v_a_2014_, v_expectedType_1983_, v_a_1982_, v___x_1984_, v_compile_1985_, v_logCompileErrors_1986_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
v___x_2017_ = 3;
lean_inc(v_a_2014_);
v___x_2018_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(v_a_2014_, v___x_2017_, v___y_1997_, v___y_1999_);
lean_dec(v___y_1997_);
lean_dec_ref(v___x_2018_);
v___x_2019_ = l_Lean_enableRealizationsForConst(v_a_2014_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v___x_2019_, 0);
lean_dec(v_unused_2027_);
v___x_2021_ = v___x_2019_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v___x_2019_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v_a_2016_);
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2016_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_a_2016_);
v_a_2028_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2019_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2019_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_dec(v_a_2014_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
return v___x_2015_;
}
}
else
{
lean_object* v___x_2037_; 
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_expectedType_1983_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v_a_1982_);
v___x_2037_ = v___x_2009_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_1982_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_expectedType_1983_);
lean_dec_ref(v_a_1982_);
v_a_2040_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2006_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2006_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_expectedType_1983_);
lean_dec_ref(v_a_1982_);
return v___x_2004_;
}
}
}
}
}
static uint64_t _init_l_Lean_Meta_normalizeInstance___closed__0(void){
_start:
{
uint8_t v___x_2202_; uint64_t v___x_2203_; 
v___x_2202_ = 3;
v___x_2203_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_Meta_normalizeInstance___closed__2(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l_Lean_Meta_normalizeInstance___closed__1));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
static double _init_l_Lean_Meta_normalizeInstance___closed__3(void){
_start:
{
lean_object* v___x_2207_; double v___x_2208_; 
v___x_2207_ = lean_unsigned_to_nat(1000000000u);
v___x_2208_ = lean_float_of_nat(v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(lean_object* v_upperBound_2209_, lean_object* v_fst_2210_, lean_object* v_args_2211_, uint8_t v___x_2212_, uint8_t v_compile_2213_, uint8_t v_logCompileErrors_2214_, uint8_t v___x_2215_, lean_object* v_a_2216_, lean_object* v_b_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_a_2224_; lean_object* v___y_2229_; uint8_t v___x_2248_; 
v___x_2248_ = lean_nat_dec_lt(v_a_2216_, v_upperBound_2209_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_b_2217_);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_array_fget_borrowed(v_fst_2210_, v_a_2216_);
v___x_2251_ = l_Lean_Expr_mvarId_x21(v___x_2250_);
lean_inc(v___x_2251_);
v___x_2252_ = l_Lean_MVarId_getDecl(v___x_2251_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v_type_2254_; lean_object* v___x_2255_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2252_);
v_type_2254_ = lean_ctor_get(v_a_2253_, 2);
lean_inc_ref(v_type_2254_);
lean_dec(v_a_2253_);
v___x_2255_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2254_, v___y_2219_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2257_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref(v___x_2255_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v_a_2256_);
v___x_2257_ = l_Lean_Meta_isProp(v_a_2256_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2259_; lean_object* v_cls_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = lean_box(0);
v_cls_2260_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_2261_ = lean_array_fget_borrowed(v_args_2211_, v_a_2216_);
v___x_2262_ = lean_unbox(v_a_2258_);
lean_dec(v_a_2258_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; 
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v_a_2256_);
v___x_2263_ = l_Lean_Meta_isClass_x3f(v_a_2256_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2365_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2365_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2365_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_a_2269_; lean_object* v___y_2272_; uint8_t v___y_2273_; lean_object* v_a_2278_; lean_object* v___y_2282_; 
if (lean_obj_tag(v_a_2264_) == 0)
{
if (v___x_2215_ == 0)
{
lean_object* v_options_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
lean_del_object(v___x_2266_);
v_options_2308_ = lean_ctor_get(v___y_2220_, 2);
v___x_2309_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2310_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; 
lean_dec(v_a_2256_);
lean_inc(v___x_2261_);
v___x_2311_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2251_, v___x_2261_, v___y_2219_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_dec_ref(v___x_2311_);
v_a_2224_ = v___x_2259_;
goto v___jp_2223_;
}
else
{
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
return v___x_2311_;
}
}
else
{
lean_object* v___x_2312_; 
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___x_2261_);
v___x_2312_ = lean_infer_type(v___x_2261_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v_a_2256_);
v___x_2314_ = l_Lean_Meta_isExprDefEq(v_a_2256_, v_a_2313_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; uint8_t v___x_2316_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref(v___x_2314_);
v___x_2316_ = lean_unbox(v_a_2315_);
lean_dec(v_a_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1));
v___x_2318_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2317_, v___y_2221_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___x_2261_);
lean_inc(v_a_2319_);
v___x_2320_ = l_Lean_Meta_mkAuxDefinition(v_a_2319_, v_a_2256_, v___x_2261_, v___x_2215_, v___x_2215_, v___x_2212_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2251_, v_a_2321_, v___y_2219_);
if (lean_obj_tag(v___x_2322_) == 0)
{
uint8_t v___x_2323_; lean_object* v___x_2324_; 
lean_dec_ref(v___x_2322_);
v___x_2323_ = 0;
lean_inc(v_a_2319_);
v___x_2324_ = l_Lean_Meta_setInlineAttribute(v_a_2319_, v___x_2323_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_dec_ref(v___x_2324_);
if (v_compile_2213_ == 0)
{
lean_object* v___x_2325_; 
lean_inc_ref(v___y_2220_);
v___x_2325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_2319_, v___x_2259_, v___x_2259_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2325_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_mk_empty_array_with_capacity(v___x_2326_);
lean_inc(v_a_2319_);
v___x_2328_ = lean_array_push(v___x_2327_, v_a_2319_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
v___x_2329_ = l_Lean_compileDecls(v___x_2328_, v_logCompileErrors_2214_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
lean_inc_ref(v___y_2220_);
v___x_2331_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_2319_, v___x_2259_, v_a_2330_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2331_;
goto v___jp_2228_;
}
else
{
lean_dec(v_a_2319_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
return v___x_2329_;
}
}
}
else
{
lean_dec(v_a_2319_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
return v___x_2324_;
}
}
else
{
lean_dec(v_a_2319_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
return v___x_2322_;
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_2319_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2332_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2320_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2320_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2340_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2318_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2318_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v___x_2348_; 
lean_dec(v_a_2256_);
lean_inc(v___x_2261_);
v___x_2348_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2251_, v___x_2261_, v___y_2219_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_dec_ref(v___x_2348_);
v_a_2224_ = v___x_2259_;
goto v___jp_2223_;
}
else
{
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
return v___x_2348_;
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2349_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2314_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2314_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
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
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2357_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2312_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2312_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
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
}
}
else
{
goto v___jp_2286_;
}
}
else
{
lean_dec_ref(v_a_2264_);
goto v___jp_2286_;
}
v___jp_2268_:
{
lean_object* v___x_2270_; 
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___x_2261_);
v___x_2270_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_2261_, v_a_2256_, v_compile_2213_, v_logCompileErrors_2214_, v___x_2251_, v___x_2259_, v_a_2269_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2270_;
goto v___jp_2228_;
}
v___jp_2271_:
{
if (v___y_2273_ == 0)
{
lean_dec_ref(v___y_2272_);
lean_del_object(v___x_2266_);
v_a_2269_ = v___x_2259_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2275_; 
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 1);
lean_ctor_set(v___x_2266_, 0, v___y_2272_);
v___x_2275_ = v___x_2266_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___y_2272_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
v___jp_2277_:
{
uint8_t v___x_2279_; 
v___x_2279_ = l_Lean_Exception_isInterrupt(v_a_2278_);
if (v___x_2279_ == 0)
{
uint8_t v___x_2280_; 
lean_inc_ref(v_a_2278_);
v___x_2280_ = l_Lean_Exception_isRuntime(v_a_2278_);
v___y_2272_ = v_a_2278_;
v___y_2273_ = v___x_2280_;
goto v___jp_2271_;
}
else
{
v___y_2272_ = v_a_2278_;
v___y_2273_ = v___x_2279_;
goto v___jp_2271_;
}
}
v___jp_2281_:
{
if (lean_obj_tag(v___y_2282_) == 0)
{
lean_object* v_a_2283_; 
lean_del_object(v___x_2266_);
v_a_2283_ = lean_ctor_get(v___y_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref(v___y_2282_);
if (lean_obj_tag(v_a_2283_) == 0)
{
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
v_a_2224_ = v___x_2259_;
goto v___jp_2223_;
}
else
{
lean_object* v_a_2284_; 
v_a_2284_ = lean_ctor_get(v_a_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref(v_a_2283_);
v_a_2269_ = v_a_2284_;
goto v___jp_2268_;
}
}
else
{
lean_object* v_a_2285_; 
v_a_2285_ = lean_ctor_get(v___y_2282_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___y_2282_);
v_a_2278_ = v_a_2285_;
goto v___jp_2277_;
}
}
v___jp_2286_:
{
lean_object* v_options_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_options_2287_ = lean_ctor_get(v___y_2220_, 2);
v___x_2288_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2289_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_del_object(v___x_2266_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___x_2261_);
v___x_2290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_2261_, v_a_2256_, v_compile_2213_, v_logCompileErrors_2214_, v___x_2251_, v___x_2259_, v___x_2259_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2290_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_box(0);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v_a_2256_);
v___x_2292_ = l_Lean_Meta_trySynthInstance(v_a_2256_, v___x_2291_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2292_);
if (lean_obj_tag(v_a_2293_) == 1)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; 
v_a_2294_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v_a_2293_);
v___x_2295_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2260_, v___y_2220_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; uint8_t v___x_2297_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = lean_unbox(v_a_2296_);
lean_dec(v_a_2296_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; 
lean_inc(v___x_2251_);
v___x_2298_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_2251_, v_a_2294_, v___x_2259_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2282_ = v___x_2298_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1);
lean_inc(v_a_2294_);
v___x_2300_ = l_Lean_MessageData_ofExpr(v_a_2294_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2260_, v___x_2301_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
lean_inc(v___x_2251_);
v___x_2304_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_2251_, v_a_2294_, v_a_2303_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2282_ = v___x_2304_;
goto v___jp_2281_;
}
else
{
lean_object* v_a_2305_; 
lean_dec(v_a_2294_);
v_a_2305_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2302_);
v_a_2278_ = v_a_2305_;
goto v___jp_2277_;
}
}
}
else
{
lean_object* v_a_2306_; 
lean_dec(v_a_2294_);
v_a_2306_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2306_);
lean_dec_ref(v___x_2295_);
v_a_2278_ = v_a_2306_;
goto v___jp_2277_;
}
}
else
{
lean_dec(v_a_2293_);
lean_del_object(v___x_2266_);
v_a_2269_ = v___x_2259_;
goto v___jp_2268_;
}
}
else
{
lean_object* v_a_2307_; 
v_a_2307_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2307_);
lean_dec_ref(v___x_2292_);
v_a_2278_ = v_a_2307_;
goto v___jp_2277_;
}
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2366_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2263_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2263_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_2374_; 
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___x_2261_);
v___x_2374_ = lean_infer_type(v___x_2261_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v_a_2375_);
lean_inc(v_a_2256_);
v___x_2376_ = l_Lean_Meta_isExprDefEq(v_a_2256_, v_a_2375_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; uint8_t v___x_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = lean_unbox(v_a_2377_);
lean_dec(v_a_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2260_, v___y_2220_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; uint8_t v___x_2381_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref(v___x_2379_);
v___x_2381_ = lean_unbox(v_a_2380_);
lean_dec(v_a_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; 
lean_dec(v_a_2375_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___x_2261_);
v___x_2382_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_2256_, v___x_2261_, v___x_2212_, v___x_2251_, v___x_2259_, v___x_2259_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2382_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2383_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3);
lean_inc(v_a_2216_);
v___x_2384_ = l_Nat_reprFast(v_a_2216_);
v___x_2385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
v___x_2386_ = l_Lean_MessageData_ofFormat(v___x_2385_);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2383_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
lean_inc(v_a_2256_);
v___x_2390_ = l_Lean_MessageData_ofExpr(v_a_2256_);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = l_Lean_MessageData_ofExpr(v_a_2375_);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
lean_inc(v___x_2261_);
v___x_2398_ = l_Lean_MessageData_ofExpr(v___x_2261_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2260_, v___x_2399_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref(v___x_2400_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___x_2261_);
v___x_2402_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_2256_, v___x_2261_, v___x_2212_, v___x_2251_, v___x_2259_, v_a_2401_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
v___y_2229_ = v___x_2402_;
goto v___jp_2228_;
}
else
{
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v_a_2375_);
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2403_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2379_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2379_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
else
{
lean_object* v___x_2411_; 
lean_dec(v_a_2375_);
lean_dec(v_a_2256_);
lean_inc(v___x_2261_);
v___x_2411_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2251_, v___x_2261_, v___y_2219_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_dec_ref(v___x_2411_);
v_a_2224_ = v___x_2259_;
goto v___jp_2223_;
}
else
{
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_a_2375_);
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2412_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2376_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2376_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2420_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2374_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2374_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_a_2256_);
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2428_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2257_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2257_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2436_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2255_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2255_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v___x_2251_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2444_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2252_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2252_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
v___jp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_unsigned_to_nat(1u);
v___x_2226_ = lean_nat_add(v_a_2216_, v___x_2225_);
lean_dec(v_a_2216_);
v_a_2216_ = v___x_2226_;
v_b_2217_ = v_a_2224_;
goto _start;
}
v___jp_2228_:
{
if (lean_obj_tag(v___y_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2239_; 
v_a_2230_ = lean_ctor_get(v___y_2229_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___y_2229_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2232_ = v___y_2229_;
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___y_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
if (lean_obj_tag(v_a_2230_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; 
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2234_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_a_2234_);
lean_dec_ref(v_a_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_a_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v_a_2238_; 
lean_del_object(v___x_2232_);
v_a_2238_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v_a_2230_);
v_a_2224_ = v_a_2238_;
goto v___jp_2223_;
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2216_);
v_a_2240_ = lean_ctor_get(v___y_2229_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___y_2229_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___y_2229_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___y_2229_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(lean_object* v_a_2452_, lean_object* v_expectedType_2453_, uint8_t v___x_2454_, uint8_t v_compile_2455_, uint8_t v_logCompileErrors_2456_, uint8_t v___x_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_, lean_object* v_x_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; 
if (lean_obj_tag(v_x_2458_) == 5)
{
lean_object* v_fn_2519_; lean_object* v_arg_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v_fn_2519_ = lean_ctor_get(v_x_2458_, 0);
lean_inc_ref(v_fn_2519_);
v_arg_2520_ = lean_ctor_get(v_x_2458_, 1);
lean_inc_ref(v_arg_2520_);
lean_dec_ref(v_x_2458_);
v___x_2521_ = lean_array_set(v_x_2459_, v_x_2460_, v_arg_2520_);
v___x_2522_ = lean_unsigned_to_nat(1u);
v___x_2523_ = lean_nat_sub(v_x_2460_, v___x_2522_);
lean_dec(v_x_2460_);
v_x_2458_ = v_fn_2519_;
v_x_2459_ = v___x_2521_;
v_x_2460_ = v___x_2523_;
goto _start;
}
else
{
lean_object* v_cls_2525_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___x_2546_; 
lean_dec(v_x_2460_);
v_cls_2525_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_2546_ = l_Lean_Expr_constName_x3f(v_x_2458_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_dec_ref(v_x_2459_);
lean_dec_ref(v_x_2458_);
v___y_2527_ = v___y_2461_;
v___y_2528_ = v___y_2462_;
v___y_2529_ = v___y_2463_;
v___y_2530_ = v___y_2464_;
goto v___jp_2526_;
}
else
{
lean_object* v_val_2547_; lean_object* v___x_2548_; 
v_val_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_val_2547_);
lean_dec_ref(v___x_2546_);
lean_inc_ref(v___y_2463_);
v___x_2548_ = l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(v_val_2547_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
if (lean_obj_tag(v_a_2549_) == 6)
{
lean_object* v_val_2550_; lean_object* v___x_2551_; 
lean_dec_ref(v_a_2452_);
v_val_2550_ = lean_ctor_get(v_a_2549_, 0);
lean_inc_ref(v_val_2550_);
lean_dec_ref(v_a_2549_);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
lean_inc_ref(v_x_2458_);
v___x_2551_ = lean_infer_type(v_x_2458_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = 0;
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
v___x_2554_ = l_Lean_Meta_forallMetaTelescope(v_a_2552_, v___x_2553_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v_snd_2556_; lean_object* v_fst_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2656_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref(v___x_2554_);
v_snd_2556_ = lean_ctor_get(v_a_2555_, 1);
v_fst_2557_ = lean_ctor_get(v_a_2555_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_a_2555_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2559_ = v_a_2555_;
v_isShared_2560_ = v_isSharedCheck_2656_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_snd_2556_);
lean_inc(v_fst_2557_);
lean_dec(v_a_2555_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2656_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_snd_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2654_; 
v_snd_2561_ = lean_ctor_get(v_snd_2556_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_snd_2556_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_snd_2556_, 0);
lean_dec(v_unused_2655_);
v___x_2563_ = v_snd_2556_;
v_isShared_2564_ = v_isSharedCheck_2654_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_snd_2561_);
lean_dec(v_snd_2556_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2654_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2565_ = lean_array_get_size(v_x_2459_);
v___x_2602_ = lean_array_get_size(v_fst_2557_);
v___x_2603_ = lean_nat_dec_eq(v___x_2565_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
lean_dec(v_snd_2561_);
lean_dec(v_fst_2557_);
lean_dec_ref(v_val_2550_);
lean_dec_ref(v_expectedType_2453_);
v___x_2604_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5);
v___x_2605_ = l_Lean_MessageData_ofExpr(v_x_2458_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set_tag(v___x_2563_, 7);
lean_ctor_set(v___x_2563_, 1, v___x_2605_);
lean_ctor_set(v___x_2563_, 0, v___x_2604_);
v___x_2607_ = v___x_2563_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7);
if (v_isShared_2560_ == 0)
{
lean_ctor_set_tag(v___x_2559_, 7);
lean_ctor_set(v___x_2559_, 1, v___x_2608_);
lean_ctor_set(v___x_2559_, 0, v___x_2607_);
v___x_2610_ = v___x_2559_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2611_ = lean_array_to_list(v_x_2459_);
v___x_2612_ = lean_box(0);
v___x_2613_ = l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(v___x_2611_, v___x_2612_);
v___x_2614_ = l_Lean_MessageData_ofList(v___x_2613_);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2610_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_2615_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v___x_2616_;
}
}
}
else
{
lean_object* v___x_2619_; 
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
lean_inc_ref(v_expectedType_2453_);
v___x_2619_ = l_Lean_Meta_isExprDefEq(v_expectedType_2453_, v_snd_2561_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; uint8_t v___x_2621_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref(v___x_2619_);
v___x_2621_ = lean_unbox(v_a_2620_);
lean_dec(v_a_2620_);
if (v___x_2621_ == 0)
{
lean_object* v_toConstantVal_2622_; lean_object* v_name_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_dec(v_fst_2557_);
lean_dec_ref(v_x_2459_);
lean_dec_ref(v_x_2458_);
v_toConstantVal_2622_ = lean_ctor_get(v_val_2550_, 0);
lean_inc_ref(v_toConstantVal_2622_);
lean_dec_ref(v_val_2550_);
v_name_2623_ = lean_ctor_get(v_toConstantVal_2622_, 0);
lean_inc(v_name_2623_);
lean_dec_ref(v_toConstantVal_2622_);
v___x_2624_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9);
v___x_2625_ = l_Lean_MessageData_ofExpr(v_expectedType_2453_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set_tag(v___x_2563_, 7);
lean_ctor_set(v___x_2563_, 1, v___x_2625_);
lean_ctor_set(v___x_2563_, 0, v___x_2624_);
v___x_2627_ = v___x_2563_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2628_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11);
if (v_isShared_2560_ == 0)
{
lean_ctor_set_tag(v___x_2559_, 7);
lean_ctor_set(v___x_2559_, 1, v___x_2628_);
lean_ctor_set(v___x_2559_, 0, v___x_2627_);
v___x_2630_ = v___x_2559_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
v___x_2631_ = l_Lean_MessageData_ofConstName(v_name_2623_, v___x_2454_);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3);
v___x_2634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2632_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_2634_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
else
{
lean_del_object(v___x_2563_);
lean_del_object(v___x_2559_);
lean_dec_ref(v_expectedType_2453_);
v___y_2567_ = v___y_2461_;
v___y_2568_ = v___y_2462_;
v___y_2569_ = v___y_2463_;
v___y_2570_ = v___y_2464_;
goto v___jp_2566_;
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_del_object(v___x_2563_);
lean_del_object(v___x_2559_);
lean_dec(v_fst_2557_);
lean_dec_ref(v_val_2550_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_x_2459_);
lean_dec_ref(v_x_2458_);
lean_dec_ref(v_expectedType_2453_);
v_a_2646_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2619_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2619_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
v___jp_2566_:
{
lean_object* v_numParams_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v_numParams_2571_ = lean_ctor_get(v_val_2550_, 3);
lean_inc(v_numParams_2571_);
lean_dec_ref(v_val_2550_);
v___x_2572_ = lean_box(0);
lean_inc(v___y_2568_);
v___x_2573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(v___x_2565_, v_fst_2557_, v_x_2459_, v___x_2457_, v_compile_2455_, v_logCompileErrors_2456_, v___x_2454_, v_numParams_2571_, v___x_2572_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec_ref(v_x_2459_);
if (lean_obj_tag(v___x_2573_) == 0)
{
size_t v_sz_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref(v___x_2573_);
v_sz_2574_ = lean_array_size(v_fst_2557_);
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_2574_, v___x_2575_, v_fst_2557_, v___y_2568_);
lean_dec(v___y_2568_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2585_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = l_Lean_mkAppN(v_x_2458_, v_a_2577_);
lean_dec(v_a_2577_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v_x_2458_);
v_a_2586_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2576_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2576_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v___y_2568_);
lean_dec(v_fst_2557_);
lean_dec_ref(v_x_2458_);
v_a_2594_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2573_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2573_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec_ref(v_val_2550_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_x_2459_);
lean_dec_ref(v_x_2458_);
lean_dec_ref(v_expectedType_2453_);
v_a_2657_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2554_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2554_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
else
{
lean_dec_ref(v_val_2550_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_x_2459_);
lean_dec_ref(v_x_2458_);
lean_dec_ref(v_expectedType_2453_);
return v___x_2551_;
}
}
else
{
lean_dec(v_a_2549_);
lean_dec_ref(v_x_2459_);
lean_dec_ref(v_x_2458_);
v___y_2527_ = v___y_2461_;
v___y_2528_ = v___y_2462_;
v___y_2529_ = v___y_2463_;
v___y_2530_ = v___y_2464_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_x_2459_);
lean_dec_ref(v_x_2458_);
lean_dec_ref(v_expectedType_2453_);
lean_dec_ref(v_a_2452_);
v_a_2665_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2548_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2548_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
v___jp_2526_:
{
lean_object* v___x_2531_; lean_object* v_a_2532_; uint8_t v___x_2533_; 
v___x_2531_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2525_, v___y_2529_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref(v___x_2531_);
v___x_2533_ = lean_unbox(v_a_2532_);
lean_dec(v_a_2532_);
if (v___x_2533_ == 0)
{
v___y_2467_ = v___y_2527_;
v___y_2468_ = v___y_2528_;
v___y_2469_ = v___y_2529_;
v___y_2470_ = v___y_2530_;
goto v___jp_2466_;
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2534_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3);
lean_inc_ref(v_a_2452_);
v___x_2535_ = l_Lean_MessageData_ofExpr(v_a_2452_);
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2525_, v___x_2536_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref(v___x_2537_);
v___y_2467_ = v___y_2527_;
v___y_2468_ = v___y_2528_;
v___y_2469_ = v___y_2529_;
v___y_2470_ = v___y_2530_;
goto v___jp_2466_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_expectedType_2453_);
lean_dec_ref(v_a_2452_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
v___jp_2466_:
{
lean_object* v_options_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v_options_2471_ = lean_ctor_get(v___y_2469_, 2);
v___x_2472_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2473_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2471_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v_expectedType_2453_);
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_a_2452_);
return v___x_2474_;
}
else
{
lean_object* v___x_2475_; 
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2469_);
lean_inc(v___y_2468_);
lean_inc_ref(v___y_2467_);
lean_inc_ref(v_a_2452_);
v___x_2475_ = lean_infer_type(v_a_2452_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___x_2475_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2469_);
lean_inc(v___y_2468_);
lean_inc_ref(v___y_2467_);
lean_inc_ref(v_expectedType_2453_);
v___x_2477_ = l_Lean_Meta_isExprDefEq(v_expectedType_2453_, v_a_2476_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2510_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2510_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2510_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_unbox(v_a_2478_);
lean_dec(v_a_2478_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_a_2485_; lean_object* v___x_2486_; 
lean_del_object(v___x_2480_);
v___x_2483_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1));
v___x_2484_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2483_, v___y_2470_);
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref(v___x_2484_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2469_);
lean_inc(v___y_2468_);
lean_inc(v_a_2485_);
v___x_2486_ = l_Lean_Meta_mkAuxDefinition(v_a_2485_, v_expectedType_2453_, v_a_2452_, v___x_2454_, v_compile_2455_, v_logCompileErrors_2456_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; uint8_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref(v___x_2486_);
v___x_2488_ = 3;
lean_inc(v_a_2485_);
v___x_2489_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(v_a_2485_, v___x_2488_, v___y_2468_, v___y_2470_);
lean_dec(v___y_2468_);
lean_dec_ref(v___x_2489_);
v___x_2490_ = l_Lean_enableRealizationsForConst(v_a_2485_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2490_, 0);
lean_dec(v_unused_2498_);
v___x_2492_ = v___x_2490_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_dec(v___x_2490_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v_a_2487_);
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2487_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_a_2487_);
v_a_2499_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2490_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2490_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_dec(v_a_2485_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
return v___x_2486_;
}
}
else
{
lean_object* v___x_2508_; 
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v_expectedType_2453_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_a_2452_);
v___x_2508_ = v___x_2480_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2452_);
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
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v_expectedType_2453_);
lean_dec_ref(v_a_2452_);
v_a_2511_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2477_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2477_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v_expectedType_2453_);
lean_dec_ref(v_a_2452_);
return v___x_2475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__1(lean_object* v_expectedType_2673_, lean_object* v_inst_2674_, uint8_t v___x_2675_, uint8_t v_compile_2676_, uint8_t v_logCompileErrors_2677_, uint8_t v_hasTrace_2678_, lean_object* v_____r_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
lean_inc(v___y_2683_);
lean_inc_ref(v___y_2682_);
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc_ref(v_expectedType_2673_);
v___x_2685_ = l_Lean_Meta_isProp(v_expectedType_2673_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2707_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2707_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2707_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
uint8_t v___x_2690_; 
v___x_2690_ = lean_unbox(v_a_2686_);
lean_dec(v_a_2686_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; 
lean_del_object(v___x_2688_);
lean_inc(v___y_2683_);
lean_inc_ref(v___y_2682_);
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
v___x_2691_ = lean_whnf(v_inst_2674_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v_dummy_2693_; lean_object* v_nargs_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
v_dummy_2693_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_2694_ = l_Lean_Expr_getAppNumArgs(v_a_2692_);
lean_inc(v_nargs_2694_);
v___x_2695_ = lean_mk_array(v_nargs_2694_, v_dummy_2693_);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_sub(v_nargs_2694_, v___x_2696_);
lean_dec(v_nargs_2694_);
lean_inc(v_a_2692_);
v___x_2698_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(v_a_2692_, v_expectedType_2673_, v___x_2675_, v_compile_2676_, v_logCompileErrors_2677_, v_hasTrace_2678_, v_a_2692_, v___x_2695_, v___x_2697_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2698_;
}
else
{
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v_expectedType_2673_);
return v___x_2691_;
}
}
else
{
lean_object* v_options_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v_options_2699_ = lean_ctor_get(v___y_2682_, 2);
v___x_2700_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2701_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2699_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2703_; 
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v_expectedType_2673_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v_inst_2674_);
v___x_2703_ = v___x_2688_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_inst_2674_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2688_);
v___x_2705_ = lean_box(0);
v___x_2706_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_2673_, v_inst_2674_, v_hasTrace_2678_, v___x_2705_, v_hasTrace_2678_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v_inst_2674_);
lean_dec_ref(v_expectedType_2673_);
v_a_2708_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2685_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2685_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(lean_object* v_upperBound_2716_, lean_object* v_fst_2717_, lean_object* v_args_2718_, uint8_t v___x_2719_, uint8_t v_compile_2720_, uint8_t v_logCompileErrors_2721_, lean_object* v_a_2722_, lean_object* v_b_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_a_2730_; lean_object* v___y_2735_; uint8_t v___x_2754_; 
v___x_2754_ = lean_nat_dec_lt(v_a_2722_, v_upperBound_2716_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_b_2723_);
return v___x_2755_;
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_array_fget_borrowed(v_fst_2717_, v_a_2722_);
v___x_2757_ = l_Lean_Expr_mvarId_x21(v___x_2756_);
lean_inc(v___x_2757_);
v___x_2758_ = l_Lean_MVarId_getDecl(v___x_2757_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v_type_2760_; lean_object* v___x_2761_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
v_type_2760_ = lean_ctor_get(v_a_2759_, 2);
lean_inc_ref(v_type_2760_);
lean_dec(v_a_2759_);
v___x_2761_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2760_, v___y_2725_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref(v___x_2761_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v_a_2762_);
v___x_2763_ = l_Lean_Meta_isProp(v_a_2762_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; lean_object* v_cls_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref(v___x_2763_);
v___x_2765_ = lean_box(0);
v_cls_2766_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_2767_ = lean_array_fget_borrowed(v_args_2718_, v_a_2722_);
v___x_2768_ = lean_unbox(v_a_2764_);
lean_dec(v_a_2764_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v_a_2762_);
v___x_2769_ = l_Lean_Meta_isClass_x3f(v_a_2762_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2873_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2873_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2873_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
if (lean_obj_tag(v_a_2770_) == 0)
{
lean_del_object(v___x_2772_);
goto v___jp_2774_;
}
else
{
lean_dec_ref(v_a_2770_);
if (v___x_2719_ == 0)
{
lean_del_object(v___x_2772_);
goto v___jp_2774_;
}
else
{
lean_object* v_options_2834_; lean_object* v_a_2836_; lean_object* v___y_2839_; uint8_t v___y_2840_; lean_object* v_a_2845_; lean_object* v___y_2849_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_options_2834_ = lean_ctor_get(v___y_2726_, 2);
v___x_2853_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2854_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2834_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_del_object(v___x_2772_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___x_2767_);
v___x_2855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_2767_, v_a_2762_, v_compile_2720_, v_logCompileErrors_2721_, v___x_2757_, v___x_2765_, v___x_2765_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
v___y_2735_ = v___x_2855_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_box(0);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v_a_2762_);
v___x_2857_ = l_Lean_Meta_trySynthInstance(v_a_2762_, v___x_2856_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2857_);
if (lean_obj_tag(v_a_2858_) == 1)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v_a_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v_a_2858_);
v___x_2860_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2766_, v___y_2726_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; uint8_t v___x_2862_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v___x_2862_ = lean_unbox(v_a_2861_);
lean_dec(v_a_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; 
lean_inc(v___x_2757_);
v___x_2863_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_2757_, v_a_2859_, v___x_2765_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
v___y_2849_ = v___x_2863_;
goto v___jp_2848_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2864_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1);
lean_inc(v_a_2859_);
v___x_2865_ = l_Lean_MessageData_ofExpr(v_a_2859_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2766_, v___x_2866_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref(v___x_2867_);
lean_inc(v___x_2757_);
v___x_2869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_2757_, v_a_2859_, v_a_2868_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
v___y_2849_ = v___x_2869_;
goto v___jp_2848_;
}
else
{
lean_object* v_a_2870_; 
lean_dec(v_a_2859_);
v_a_2870_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2867_);
v_a_2845_ = v_a_2870_;
goto v___jp_2844_;
}
}
}
else
{
lean_object* v_a_2871_; 
lean_dec(v_a_2859_);
v_a_2871_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v___x_2860_);
v_a_2845_ = v_a_2871_;
goto v___jp_2844_;
}
}
else
{
lean_dec(v_a_2858_);
lean_del_object(v___x_2772_);
v_a_2836_ = v___x_2765_;
goto v___jp_2835_;
}
}
else
{
lean_object* v_a_2872_; 
v_a_2872_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2857_);
v_a_2845_ = v_a_2872_;
goto v___jp_2844_;
}
}
v___jp_2835_:
{
lean_object* v___x_2837_; 
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___x_2767_);
v___x_2837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_2767_, v_a_2762_, v_compile_2720_, v_logCompileErrors_2721_, v___x_2757_, v___x_2765_, v_a_2836_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
v___y_2735_ = v___x_2837_;
goto v___jp_2734_;
}
v___jp_2838_:
{
if (v___y_2840_ == 0)
{
lean_dec_ref(v___y_2839_);
lean_del_object(v___x_2772_);
v_a_2836_ = v___x_2765_;
goto v___jp_2835_;
}
else
{
lean_object* v___x_2842_; 
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 1);
lean_ctor_set(v___x_2772_, 0, v___y_2839_);
v___x_2842_ = v___x_2772_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___y_2839_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
v___jp_2844_:
{
uint8_t v___x_2846_; 
v___x_2846_ = l_Lean_Exception_isInterrupt(v_a_2845_);
if (v___x_2846_ == 0)
{
uint8_t v___x_2847_; 
lean_inc_ref(v_a_2845_);
v___x_2847_ = l_Lean_Exception_isRuntime(v_a_2845_);
v___y_2839_ = v_a_2845_;
v___y_2840_ = v___x_2847_;
goto v___jp_2838_;
}
else
{
v___y_2839_ = v_a_2845_;
v___y_2840_ = v___x_2846_;
goto v___jp_2838_;
}
}
v___jp_2848_:
{
if (lean_obj_tag(v___y_2849_) == 0)
{
lean_object* v_a_2850_; 
lean_del_object(v___x_2772_);
v_a_2850_ = lean_ctor_get(v___y_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___y_2849_);
if (lean_obj_tag(v_a_2850_) == 0)
{
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
v_a_2730_ = v___x_2765_;
goto v___jp_2729_;
}
else
{
lean_object* v_a_2851_; 
v_a_2851_ = lean_ctor_get(v_a_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v_a_2850_);
v_a_2836_ = v_a_2851_;
goto v___jp_2835_;
}
}
else
{
lean_object* v_a_2852_; 
v_a_2852_ = lean_ctor_get(v___y_2849_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___y_2849_);
v_a_2845_ = v_a_2852_;
goto v___jp_2844_;
}
}
}
}
v___jp_2774_:
{
lean_object* v_options_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v_options_2775_ = lean_ctor_get(v___y_2726_, 2);
v___x_2776_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2777_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2775_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
lean_dec(v_a_2762_);
lean_inc(v___x_2767_);
v___x_2778_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2757_, v___x_2767_, v___y_2725_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_dec_ref(v___x_2778_);
v_a_2730_ = v___x_2765_;
goto v___jp_2729_;
}
else
{
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
return v___x_2778_;
}
}
else
{
lean_object* v___x_2779_; 
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___x_2767_);
v___x_2779_ = lean_infer_type(v___x_2767_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref(v___x_2779_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v_a_2762_);
v___x_2781_ = l_Lean_Meta_isExprDefEq(v_a_2762_, v_a_2780_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; uint8_t v___x_2783_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref(v___x_2781_);
v___x_2783_ = lean_unbox(v_a_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1));
v___x_2785_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2784_, v___y_2727_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; uint8_t v___x_2787_; uint8_t v___x_2788_; lean_object* v___x_2789_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = lean_unbox(v_a_2782_);
v___x_2788_ = lean_unbox(v_a_2782_);
lean_dec(v_a_2782_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___x_2767_);
lean_inc(v_a_2786_);
v___x_2789_ = l_Lean_Meta_mkAuxDefinition(v_a_2786_, v_a_2762_, v___x_2767_, v___x_2787_, v___x_2788_, v___x_2719_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2757_, v_a_2790_, v___y_2725_);
if (lean_obj_tag(v___x_2791_) == 0)
{
uint8_t v___x_2792_; lean_object* v___x_2793_; 
lean_dec_ref(v___x_2791_);
v___x_2792_ = 0;
lean_inc(v_a_2786_);
v___x_2793_ = l_Lean_Meta_setInlineAttribute(v_a_2786_, v___x_2792_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_dec_ref(v___x_2793_);
if (v_compile_2720_ == 0)
{
lean_object* v___x_2794_; 
lean_inc_ref(v___y_2726_);
v___x_2794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_2786_, v___x_2765_, v___x_2765_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
v___y_2735_ = v___x_2794_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = lean_mk_empty_array_with_capacity(v___x_2795_);
lean_inc(v_a_2786_);
v___x_2797_ = lean_array_push(v___x_2796_, v_a_2786_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
v___x_2798_ = l_Lean_compileDecls(v___x_2797_, v_logCompileErrors_2721_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2800_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref(v___x_2798_);
lean_inc_ref(v___y_2726_);
v___x_2800_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_2786_, v___x_2765_, v_a_2799_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
v___y_2735_ = v___x_2800_;
goto v___jp_2734_;
}
else
{
lean_dec(v_a_2786_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
return v___x_2798_;
}
}
}
else
{
lean_dec(v_a_2786_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
return v___x_2793_;
}
}
else
{
lean_dec(v_a_2786_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
return v___x_2791_;
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2786_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2801_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2789_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2789_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2782_);
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2809_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2785_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2785_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v___x_2817_; 
lean_dec(v_a_2782_);
lean_dec(v_a_2762_);
lean_inc(v___x_2767_);
v___x_2817_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2757_, v___x_2767_, v___y_2725_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_dec_ref(v___x_2817_);
v_a_2730_ = v___x_2765_;
goto v___jp_2729_;
}
else
{
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
return v___x_2817_;
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2818_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2781_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2781_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2826_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2779_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2779_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2874_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2769_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2769_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
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
else
{
lean_object* v___x_2882_; 
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___x_2767_);
v___x_2882_ = lean_infer_type(v___x_2767_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v_a_2883_);
lean_inc(v_a_2762_);
v___x_2884_ = l_Lean_Meta_isExprDefEq(v_a_2762_, v_a_2883_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; uint8_t v___x_2886_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref(v___x_2884_);
v___x_2886_ = lean_unbox(v_a_2885_);
lean_dec(v_a_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2766_, v___y_2726_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; uint8_t v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = lean_unbox(v_a_2888_);
lean_dec(v_a_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v_a_2883_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___x_2767_);
v___x_2890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_2762_, v___x_2767_, v___x_2719_, v___x_2757_, v___x_2765_, v___x_2765_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
v___y_2735_ = v___x_2890_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2891_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3);
lean_inc(v_a_2722_);
v___x_2892_ = l_Nat_reprFast(v_a_2722_);
v___x_2893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
v___x_2894_ = l_Lean_MessageData_ofFormat(v___x_2893_);
v___x_2895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2891_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
lean_inc(v_a_2762_);
v___x_2898_ = l_Lean_MessageData_ofExpr(v_a_2762_);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Lean_MessageData_ofExpr(v_a_2883_);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
lean_inc(v___x_2767_);
v___x_2906_ = l_Lean_MessageData_ofExpr(v___x_2767_);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2766_, v___x_2907_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2910_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2908_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___x_2767_);
v___x_2910_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_2762_, v___x_2767_, v___x_2719_, v___x_2757_, v___x_2765_, v_a_2909_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
v___y_2735_ = v___x_2910_;
goto v___jp_2734_;
}
else
{
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
return v___x_2908_;
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_a_2883_);
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2911_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2887_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2887_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v___x_2919_; 
lean_dec(v_a_2883_);
lean_dec(v_a_2762_);
lean_inc(v___x_2767_);
v___x_2919_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2757_, v___x_2767_, v___y_2725_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_dec_ref(v___x_2919_);
v_a_2730_ = v___x_2765_;
goto v___jp_2729_;
}
else
{
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
return v___x_2919_;
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_a_2883_);
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2920_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2884_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2884_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2928_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2882_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2882_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_a_2762_);
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2936_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2763_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2763_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2944_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2761_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2761_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v___x_2757_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2952_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2758_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2758_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
v___jp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(1u);
v___x_2732_ = lean_nat_add(v_a_2722_, v___x_2731_);
lean_dec(v_a_2722_);
v_a_2722_ = v___x_2732_;
v_b_2723_ = v_a_2730_;
goto _start;
}
v___jp_2734_:
{
if (lean_obj_tag(v___y_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2745_; 
v_a_2736_ = lean_ctor_get(v___y_2735_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___y_2735_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2738_ = v___y_2735_;
v_isShared_2739_ = v_isSharedCheck_2745_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___y_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2745_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
if (lean_obj_tag(v_a_2736_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; 
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2740_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_a_2740_);
lean_dec_ref(v_a_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v_a_2740_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
else
{
lean_object* v_a_2744_; 
lean_del_object(v___x_2738_);
v_a_2744_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v_a_2736_);
v_a_2730_ = v_a_2744_;
goto v___jp_2729_;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_a_2722_);
v_a_2746_ = lean_ctor_get(v___y_2735_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___y_2735_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___y_2735_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___y_2735_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15(lean_object* v_a_2960_, lean_object* v_expectedType_2961_, uint8_t v_compile_2962_, uint8_t v_logCompileErrors_2963_, uint8_t v___x_2964_, lean_object* v_x_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; 
if (lean_obj_tag(v_x_2965_) == 5)
{
lean_object* v_fn_3027_; lean_object* v_arg_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_fn_3027_ = lean_ctor_get(v_x_2965_, 0);
lean_inc_ref(v_fn_3027_);
v_arg_3028_ = lean_ctor_get(v_x_2965_, 1);
lean_inc_ref(v_arg_3028_);
lean_dec_ref(v_x_2965_);
v___x_3029_ = lean_array_set(v_x_2966_, v_x_2967_, v_arg_3028_);
v___x_3030_ = lean_unsigned_to_nat(1u);
v___x_3031_ = lean_nat_sub(v_x_2967_, v___x_3030_);
lean_dec(v_x_2967_);
v_x_2965_ = v_fn_3027_;
v_x_2966_ = v___x_3029_;
v_x_2967_ = v___x_3031_;
goto _start;
}
else
{
lean_object* v_cls_3033_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___x_3054_; 
lean_dec(v_x_2967_);
v_cls_3033_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_3054_ = l_Lean_Expr_constName_x3f(v_x_2965_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_dec_ref(v_x_2966_);
lean_dec_ref(v_x_2965_);
v___y_3035_ = v___y_2968_;
v___y_3036_ = v___y_2969_;
v___y_3037_ = v___y_2970_;
v___y_3038_ = v___y_2971_;
goto v___jp_3034_;
}
else
{
lean_object* v_val_3055_; lean_object* v___x_3056_; 
v_val_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_val_3055_);
lean_dec_ref(v___x_3054_);
lean_inc_ref(v___y_2970_);
v___x_3056_ = l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(v_val_3055_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref(v___x_3056_);
if (lean_obj_tag(v_a_3057_) == 6)
{
lean_object* v_val_3058_; lean_object* v___x_3059_; 
lean_dec_ref(v_a_2960_);
v_val_3058_ = lean_ctor_get(v_a_3057_, 0);
lean_inc_ref(v_val_3058_);
lean_dec_ref(v_a_3057_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
lean_inc_ref(v_x_2965_);
v___x_3059_ = lean_infer_type(v_x_2965_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref(v___x_3059_);
v___x_3061_ = 0;
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
v___x_3062_ = l_Lean_Meta_forallMetaTelescope(v_a_3060_, v___x_3061_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v_snd_3064_; lean_object* v_fst_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3165_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref(v___x_3062_);
v_snd_3064_ = lean_ctor_get(v_a_3063_, 1);
v_fst_3065_ = lean_ctor_get(v_a_3063_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_a_3063_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3067_ = v_a_3063_;
v_isShared_3068_ = v_isSharedCheck_3165_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_snd_3064_);
lean_inc(v_fst_3065_);
lean_dec(v_a_3063_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3165_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v_snd_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3163_; 
v_snd_3069_ = lean_ctor_get(v_snd_3064_, 1);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_snd_3064_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v_snd_3064_, 0);
lean_dec(v_unused_3164_);
v___x_3071_ = v_snd_3064_;
v_isShared_3072_ = v_isSharedCheck_3163_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_snd_3069_);
lean_dec(v_snd_3064_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3163_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3073_ = lean_array_get_size(v_x_2966_);
v___x_3110_ = lean_array_get_size(v_fst_3065_);
v___x_3111_ = lean_nat_dec_eq(v___x_3073_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
lean_dec(v_snd_3069_);
lean_dec(v_fst_3065_);
lean_dec_ref(v_val_3058_);
lean_dec_ref(v_expectedType_2961_);
v___x_3112_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__5);
v___x_3113_ = l_Lean_MessageData_ofExpr(v_x_2965_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 7);
lean_ctor_set(v___x_3071_, 1, v___x_3113_);
lean_ctor_set(v___x_3071_, 0, v___x_3112_);
v___x_3115_ = v___x_3071_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__7);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 7);
lean_ctor_set(v___x_3067_, 1, v___x_3116_);
lean_ctor_set(v___x_3067_, 0, v___x_3115_);
v___x_3118_ = v___x_3067_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3119_ = lean_array_to_list(v_x_2966_);
v___x_3120_ = lean_box(0);
v___x_3121_ = l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(v___x_3119_, v___x_3120_);
v___x_3122_ = l_Lean_MessageData_ofList(v___x_3121_);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3118_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_3123_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
return v___x_3124_;
}
}
}
else
{
lean_object* v___x_3127_; 
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
lean_inc_ref(v_expectedType_2961_);
v___x_3127_ = l_Lean_Meta_isExprDefEq(v_expectedType_2961_, v_snd_3069_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; uint8_t v___x_3129_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = lean_unbox(v_a_3128_);
if (v___x_3129_ == 0)
{
lean_object* v_toConstantVal_3130_; lean_object* v_name_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
lean_dec(v_fst_3065_);
lean_dec_ref(v_x_2966_);
lean_dec_ref(v_x_2965_);
v_toConstantVal_3130_ = lean_ctor_get(v_val_3058_, 0);
lean_inc_ref(v_toConstantVal_3130_);
lean_dec_ref(v_val_3058_);
v_name_3131_ = lean_ctor_get(v_toConstantVal_3130_, 0);
lean_inc(v_name_3131_);
lean_dec_ref(v_toConstantVal_3130_);
v___x_3132_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__9);
v___x_3133_ = l_Lean_MessageData_ofExpr(v_expectedType_2961_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 7);
lean_ctor_set(v___x_3071_, 1, v___x_3133_);
lean_ctor_set(v___x_3071_, 0, v___x_3132_);
v___x_3135_ = v___x_3071_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__11);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 7);
lean_ctor_set(v___x_3067_, 1, v___x_3136_);
lean_ctor_set(v___x_3067_, 0, v___x_3135_);
v___x_3138_ = v___x_3067_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v___x_3139_ = lean_unbox(v_a_3128_);
lean_dec(v_a_3128_);
v___x_3140_ = l_Lean_MessageData_ofConstName(v_name_3131_, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3138_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3);
v___x_3143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3141_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_3143_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
else
{
lean_dec(v_a_3128_);
lean_del_object(v___x_3071_);
lean_del_object(v___x_3067_);
lean_dec_ref(v_expectedType_2961_);
v___y_3075_ = v___y_2968_;
v___y_3076_ = v___y_2969_;
v___y_3077_ = v___y_2970_;
v___y_3078_ = v___y_2971_;
goto v___jp_3074_;
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_del_object(v___x_3071_);
lean_del_object(v___x_3067_);
lean_dec(v_fst_3065_);
lean_dec_ref(v_val_3058_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v_x_2966_);
lean_dec_ref(v_x_2965_);
lean_dec_ref(v_expectedType_2961_);
v_a_3155_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3127_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3127_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
v___jp_3074_:
{
lean_object* v_numParams_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v_numParams_3079_ = lean_ctor_get(v_val_3058_, 3);
lean_inc(v_numParams_3079_);
lean_dec_ref(v_val_3058_);
v___x_3080_ = lean_box(0);
lean_inc(v___y_3076_);
v___x_3081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(v___x_3073_, v_fst_3065_, v_x_2966_, v___x_2964_, v_compile_2962_, v_logCompileErrors_2963_, v_numParams_3079_, v___x_3080_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec_ref(v_x_2966_);
if (lean_obj_tag(v___x_3081_) == 0)
{
size_t v_sz_3082_; size_t v___x_3083_; lean_object* v___x_3084_; 
lean_dec_ref(v___x_3081_);
v_sz_3082_ = lean_array_size(v_fst_3065_);
v___x_3083_ = ((size_t)0ULL);
v___x_3084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_3082_, v___x_3083_, v_fst_3065_, v___y_3076_);
lean_dec(v___y_3076_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3093_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = l_Lean_mkAppN(v_x_2965_, v_a_3085_);
lean_dec(v_a_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3089_);
v___x_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v_x_2965_);
v_a_3094_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3084_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3084_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
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
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v___y_3076_);
lean_dec(v_fst_3065_);
lean_dec_ref(v_x_2965_);
v_a_3102_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3081_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3081_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref(v_val_3058_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v_x_2966_);
lean_dec_ref(v_x_2965_);
lean_dec_ref(v_expectedType_2961_);
v_a_3166_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3062_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3062_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
else
{
lean_dec_ref(v_val_3058_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v_x_2966_);
lean_dec_ref(v_x_2965_);
lean_dec_ref(v_expectedType_2961_);
return v___x_3059_;
}
}
else
{
lean_dec(v_a_3057_);
lean_dec_ref(v_x_2966_);
lean_dec_ref(v_x_2965_);
v___y_3035_ = v___y_2968_;
v___y_3036_ = v___y_2969_;
v___y_3037_ = v___y_2970_;
v___y_3038_ = v___y_2971_;
goto v___jp_3034_;
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v_x_2966_);
lean_dec_ref(v_x_2965_);
lean_dec_ref(v_expectedType_2961_);
lean_dec_ref(v_a_2960_);
v_a_3174_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3056_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3056_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
v___jp_3034_:
{
lean_object* v___x_3039_; lean_object* v_a_3040_; uint8_t v___x_3041_; 
v___x_3039_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3033_, v___y_3037_);
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref(v___x_3039_);
v___x_3041_ = lean_unbox(v_a_3040_);
lean_dec(v_a_3040_);
if (v___x_3041_ == 0)
{
v___y_2974_ = v___y_3035_;
v___y_2975_ = v___y_3036_;
v___y_2976_ = v___y_3037_;
v___y_2977_ = v___y_3038_;
goto v___jp_2973_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3042_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__3);
lean_inc_ref(v_a_2960_);
v___x_3043_ = l_Lean_MessageData_ofExpr(v_a_2960_);
v___x_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3033_, v___x_3044_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_dec_ref(v___x_3045_);
v___y_2974_ = v___y_3035_;
v___y_2975_ = v___y_3036_;
v___y_2976_ = v___y_3037_;
v___y_2977_ = v___y_3038_;
goto v___jp_2973_;
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v_expectedType_2961_);
lean_dec_ref(v_a_2960_);
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
}
v___jp_2973_:
{
lean_object* v_options_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v_options_2978_ = lean_ctor_get(v___y_2976_, 2);
v___x_2979_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2980_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; 
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec_ref(v_expectedType_2961_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_a_2960_);
return v___x_2981_;
}
else
{
lean_object* v___x_2982_; 
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc_ref(v_a_2960_);
v___x_2982_ = lean_infer_type(v_a_2960_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc_ref(v_expectedType_2961_);
v___x_2984_ = l_Lean_Meta_isExprDefEq(v_expectedType_2961_, v_a_2983_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3018_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2987_ = v___x_2984_;
v_isShared_2988_ = v_isSharedCheck_3018_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3018_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_unbox(v_a_2985_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v_a_2992_; uint8_t v___x_2993_; lean_object* v___x_2994_; 
lean_del_object(v___x_2987_);
v___x_2990_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___closed__1));
v___x_2991_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2990_, v___y_2977_);
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = lean_unbox(v_a_2985_);
lean_dec(v_a_2985_);
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc(v_a_2992_);
v___x_2994_ = l_Lean_Meta_mkAuxDefinition(v_a_2992_, v_expectedType_2961_, v_a_2960_, v___x_2993_, v_compile_2962_, v_logCompileErrors_2963_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = 3;
lean_inc(v_a_2992_);
v___x_2997_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(v_a_2992_, v___x_2996_, v___y_2975_, v___y_2977_);
lean_dec(v___y_2975_);
lean_dec_ref(v___x_2997_);
v___x_2998_ = l_Lean_enableRealizationsForConst(v_a_2992_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
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
lean_ctor_set(v___x_3000_, 0, v_a_2995_);
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2995_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v_a_2995_);
v_a_3007_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2998_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2998_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_dec(v_a_2992_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
return v___x_2994_;
}
}
else
{
lean_object* v___x_3016_; 
lean_dec(v_a_2985_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec_ref(v_expectedType_2961_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v_a_2960_);
v___x_3016_ = v___x_2987_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_2960_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec_ref(v_expectedType_2961_);
lean_dec_ref(v_a_2960_);
v_a_3019_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2984_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2984_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec_ref(v_expectedType_2961_);
lean_dec_ref(v_a_2960_);
return v___x_2982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__2(lean_object* v_expectedType_3182_, lean_object* v_inst_3183_, uint8_t v_compile_3184_, uint8_t v_logCompileErrors_3185_, uint8_t v___x_3186_, lean_object* v_____r_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3193_; 
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc_ref(v_expectedType_3182_);
v___x_3193_ = l_Lean_Meta_isProp(v_expectedType_3182_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3215_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3215_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3215_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
uint8_t v___x_3198_; 
v___x_3198_ = lean_unbox(v_a_3194_);
lean_dec(v_a_3194_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; 
lean_del_object(v___x_3196_);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
v___x_3199_ = lean_whnf(v_inst_3183_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v_dummy_3201_; lean_object* v_nargs_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref(v___x_3199_);
v_dummy_3201_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_3202_ = l_Lean_Expr_getAppNumArgs(v_a_3200_);
lean_inc(v_nargs_3202_);
v___x_3203_ = lean_mk_array(v_nargs_3202_, v_dummy_3201_);
v___x_3204_ = lean_unsigned_to_nat(1u);
v___x_3205_ = lean_nat_sub(v_nargs_3202_, v___x_3204_);
lean_dec(v_nargs_3202_);
lean_inc(v_a_3200_);
v___x_3206_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15(v_a_3200_, v_expectedType_3182_, v_compile_3184_, v_logCompileErrors_3185_, v___x_3186_, v_a_3200_, v___x_3203_, v___x_3205_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3206_;
}
else
{
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec_ref(v_expectedType_3182_);
return v___x_3199_;
}
}
else
{
lean_object* v_options_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_options_3207_ = lean_ctor_get(v___y_3190_, 2);
v___x_3208_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3209_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3211_; 
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec_ref(v_expectedType_3182_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v_inst_3183_);
v___x_3211_ = v___x_3196_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_inst_3183_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_del_object(v___x_3196_);
v___x_3213_ = lean_box(0);
v___x_3214_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_3182_, v_inst_3183_, v___x_3186_, v___x_3213_, v___x_3186_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec_ref(v_inst_3183_);
lean_dec_ref(v_expectedType_3182_);
v_a_3216_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3193_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3193_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance(lean_object* v_inst_3224_, lean_object* v_expectedType_3225_, uint8_t v_compile_3226_, uint8_t v_logCompileErrors_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v___x_3233_; lean_object* v_options_3234_; uint8_t v_foApprox_3235_; uint8_t v_ctxApprox_3236_; uint8_t v_quasiPatternApprox_3237_; uint8_t v_constApprox_3238_; uint8_t v_isDefEqStuckEx_3239_; uint8_t v_unificationHints_3240_; uint8_t v_proofIrrelevance_3241_; uint8_t v_assignSyntheticOpaque_3242_; uint8_t v_offsetCnstrs_3243_; uint8_t v_etaStruct_3244_; uint8_t v_univApprox_3245_; uint8_t v_iota_3246_; uint8_t v_beta_3247_; uint8_t v_proj_3248_; uint8_t v_zeta_3249_; uint8_t v_zetaDelta_3250_; uint8_t v_zetaUnused_3251_; uint8_t v_zetaHave_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3572_; 
v___x_3233_ = l_Lean_Meta_Context_config(v_a_3228_);
v_options_3234_ = lean_ctor_get(v_a_3230_, 2);
v_foApprox_3235_ = lean_ctor_get_uint8(v___x_3233_, 0);
v_ctxApprox_3236_ = lean_ctor_get_uint8(v___x_3233_, 1);
v_quasiPatternApprox_3237_ = lean_ctor_get_uint8(v___x_3233_, 2);
v_constApprox_3238_ = lean_ctor_get_uint8(v___x_3233_, 3);
v_isDefEqStuckEx_3239_ = lean_ctor_get_uint8(v___x_3233_, 4);
v_unificationHints_3240_ = lean_ctor_get_uint8(v___x_3233_, 5);
v_proofIrrelevance_3241_ = lean_ctor_get_uint8(v___x_3233_, 6);
v_assignSyntheticOpaque_3242_ = lean_ctor_get_uint8(v___x_3233_, 7);
v_offsetCnstrs_3243_ = lean_ctor_get_uint8(v___x_3233_, 8);
v_etaStruct_3244_ = lean_ctor_get_uint8(v___x_3233_, 10);
v_univApprox_3245_ = lean_ctor_get_uint8(v___x_3233_, 11);
v_iota_3246_ = lean_ctor_get_uint8(v___x_3233_, 12);
v_beta_3247_ = lean_ctor_get_uint8(v___x_3233_, 13);
v_proj_3248_ = lean_ctor_get_uint8(v___x_3233_, 14);
v_zeta_3249_ = lean_ctor_get_uint8(v___x_3233_, 15);
v_zetaDelta_3250_ = lean_ctor_get_uint8(v___x_3233_, 16);
v_zetaUnused_3251_ = lean_ctor_get_uint8(v___x_3233_, 17);
v_zetaHave_3252_ = lean_ctor_get_uint8(v___x_3233_, 18);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3254_ = v___x_3233_;
v_isShared_3255_ = v_isSharedCheck_3572_;
goto v_resetjp_3253_;
}
else
{
lean_dec(v___x_3233_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3572_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
uint8_t v_trackZetaDelta_3256_; lean_object* v_zetaDeltaSet_3257_; lean_object* v_lctx_3258_; lean_object* v_localInstances_3259_; lean_object* v_defEqCtx_x3f_3260_; lean_object* v_synthPendingDepth_3261_; lean_object* v_canUnfold_x3f_3262_; uint8_t v_univApprox_3263_; uint8_t v_inTypeClassResolution_3264_; uint8_t v_cacheInferType_3265_; uint8_t v_hasTrace_3266_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; uint8_t v___x_3303_; lean_object* v_config_3305_; 
v_trackZetaDelta_3256_ = lean_ctor_get_uint8(v_a_3228_, sizeof(void*)*7);
v_zetaDeltaSet_3257_ = lean_ctor_get(v_a_3228_, 1);
lean_inc(v_zetaDeltaSet_3257_);
v_lctx_3258_ = lean_ctor_get(v_a_3228_, 2);
lean_inc_ref(v_lctx_3258_);
v_localInstances_3259_ = lean_ctor_get(v_a_3228_, 3);
lean_inc_ref(v_localInstances_3259_);
v_defEqCtx_x3f_3260_ = lean_ctor_get(v_a_3228_, 4);
lean_inc(v_defEqCtx_x3f_3260_);
v_synthPendingDepth_3261_ = lean_ctor_get(v_a_3228_, 5);
lean_inc(v_synthPendingDepth_3261_);
v_canUnfold_x3f_3262_ = lean_ctor_get(v_a_3228_, 6);
lean_inc(v_canUnfold_x3f_3262_);
v_univApprox_3263_ = lean_ctor_get_uint8(v_a_3228_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3264_ = lean_ctor_get_uint8(v_a_3228_, sizeof(void*)*7 + 2);
v_cacheInferType_3265_ = lean_ctor_get_uint8(v_a_3228_, sizeof(void*)*7 + 3);
v_hasTrace_3266_ = lean_ctor_get_uint8(v_options_3234_, sizeof(void*)*1);
v___x_3303_ = 3;
if (v_isShared_3255_ == 0)
{
v_config_3305_ = v___x_3254_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 0, v_foApprox_3235_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 1, v_ctxApprox_3236_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 2, v_quasiPatternApprox_3237_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 3, v_constApprox_3238_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 4, v_isDefEqStuckEx_3239_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 5, v_unificationHints_3240_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 6, v_proofIrrelevance_3241_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 7, v_assignSyntheticOpaque_3242_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 8, v_offsetCnstrs_3243_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 10, v_etaStruct_3244_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 11, v_univApprox_3245_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 12, v_iota_3246_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 13, v_beta_3247_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 14, v_proj_3248_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 15, v_zeta_3249_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 16, v_zetaDelta_3250_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 17, v_zetaUnused_3251_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, 18, v_zetaHave_3252_);
v_config_3305_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3304_;
}
v___jp_3267_:
{
lean_object* v___x_3272_; 
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
lean_inc(v___y_3269_);
lean_inc_ref(v___y_3268_);
lean_inc_ref(v_expectedType_3225_);
v___x_3272_ = l_Lean_Meta_isProp(v_expectedType_3225_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3294_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3294_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3294_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_unbox(v_a_3273_);
lean_dec(v_a_3273_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_del_object(v___x_3275_);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
lean_inc(v___y_3269_);
lean_inc_ref(v___y_3268_);
v___x_3278_ = lean_whnf(v_inst_3224_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v_dummy_3280_; lean_object* v_nargs_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref(v___x_3278_);
v_dummy_3280_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_3281_ = l_Lean_Expr_getAppNumArgs(v_a_3279_);
lean_inc(v_nargs_3281_);
v___x_3282_ = lean_mk_array(v_nargs_3281_, v_dummy_3280_);
v___x_3283_ = lean_unsigned_to_nat(1u);
v___x_3284_ = lean_nat_sub(v_nargs_3281_, v___x_3283_);
lean_dec(v_nargs_3281_);
lean_inc(v_a_3279_);
v___x_3285_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10(v_a_3279_, v_expectedType_3225_, v_hasTrace_3266_, v_compile_3226_, v_logCompileErrors_3227_, v_a_3279_, v___x_3282_, v___x_3284_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
return v___x_3285_;
}
else
{
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v_expectedType_3225_);
return v___x_3278_;
}
}
else
{
lean_object* v_options_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
v_options_3286_ = lean_ctor_get(v___y_3270_, 2);
v___x_3287_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3288_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3286_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3290_; 
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v_expectedType_3225_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v_inst_3224_);
v___x_3290_ = v___x_3275_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_inst_3224_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_del_object(v___x_3275_);
v___x_3292_ = lean_box(0);
v___x_3293_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_3225_, v_inst_3224_, v___x_3288_, v___x_3292_, v___x_3288_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
return v___x_3293_;
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3295_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3272_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3272_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
v_reusejp_3304_:
{
uint64_t v___x_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3563_; 
lean_ctor_set_uint8(v_config_3305_, 9, v___x_3303_);
v___x_3306_ = l_Lean_Meta_Context_configKey(v_a_3228_);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_a_3228_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; lean_object* v_unused_3565_; lean_object* v_unused_3566_; lean_object* v_unused_3567_; lean_object* v_unused_3568_; lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3564_ = lean_ctor_get(v_a_3228_, 6);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_a_3228_, 5);
lean_dec(v_unused_3565_);
v_unused_3566_ = lean_ctor_get(v_a_3228_, 4);
lean_dec(v_unused_3566_);
v_unused_3567_ = lean_ctor_get(v_a_3228_, 3);
lean_dec(v_unused_3567_);
v_unused_3568_ = lean_ctor_get(v_a_3228_, 2);
lean_dec(v_unused_3568_);
v_unused_3569_ = lean_ctor_get(v_a_3228_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_a_3228_, 0);
lean_dec(v_unused_3570_);
v___x_3308_ = v_a_3228_;
v_isShared_3309_ = v_isSharedCheck_3563_;
goto v_resetjp_3307_;
}
else
{
lean_dec(v_a_3228_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3563_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
uint64_t v___x_3310_; uint64_t v___x_3311_; lean_object* v_cls_3312_; uint64_t v___x_3313_; uint64_t v___x_3314_; uint64_t v_key_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3310_ = 2ULL;
v___x_3311_ = lean_uint64_shift_right(v___x_3306_, v___x_3310_);
v_cls_3312_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_3313_ = lean_uint64_shift_left(v___x_3311_, v___x_3310_);
v___x_3314_ = lean_uint64_once(&l_Lean_Meta_normalizeInstance___closed__0, &l_Lean_Meta_normalizeInstance___closed__0_once, _init_l_Lean_Meta_normalizeInstance___closed__0);
v_key_3315_ = lean_uint64_lor(v___x_3313_, v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3316_, 0, v_config_3305_);
lean_ctor_set_uint64(v___x_3316_, sizeof(void*)*1, v_key_3315_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3316_);
v___x_3318_ = v___x_3308_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_zetaDeltaSet_3257_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_lctx_3258_);
lean_ctor_set(v_reuseFailAlloc_3562_, 3, v_localInstances_3259_);
lean_ctor_set(v_reuseFailAlloc_3562_, 4, v_defEqCtx_x3f_3260_);
lean_ctor_set(v_reuseFailAlloc_3562_, 5, v_synthPendingDepth_3261_);
lean_ctor_set(v_reuseFailAlloc_3562_, 6, v_canUnfold_x3f_3262_);
lean_ctor_set_uint8(v_reuseFailAlloc_3562_, sizeof(void*)*7, v_trackZetaDelta_3256_);
lean_ctor_set_uint8(v_reuseFailAlloc_3562_, sizeof(void*)*7 + 1, v_univApprox_3263_);
lean_ctor_set_uint8(v_reuseFailAlloc_3562_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3264_);
lean_ctor_set_uint8(v_reuseFailAlloc_3562_, sizeof(void*)*7 + 3, v_cacheInferType_3265_);
v___x_3318_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
if (v_hasTrace_3266_ == 0)
{
lean_object* v___x_3319_; 
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v___x_3318_);
lean_inc_ref(v_expectedType_3225_);
v___x_3319_ = l_Lean_Meta_isClass_x3f(v_expectedType_3225_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3351_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3351_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3351_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
if (lean_obj_tag(v_a_3320_) == 1)
{
lean_object* v_val_3324_; lean_object* v___x_3325_; 
lean_del_object(v___x_3322_);
v_val_3324_ = lean_ctor_get(v_a_3320_, 0);
lean_inc(v_val_3324_);
lean_dec_ref(v_a_3320_);
v___x_3325_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3312_, v_a_3230_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; uint8_t v___x_3327_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref(v___x_3325_);
v___x_3327_ = lean_unbox(v_a_3326_);
lean_dec(v_a_3326_);
if (v___x_3327_ == 0)
{
lean_dec(v_val_3324_);
v___y_3268_ = v___x_3318_;
v___y_3269_ = v_a_3229_;
v___y_3270_ = v_a_3230_;
v___y_3271_ = v_a_3231_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3328_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___closed__2, &l_Lean_Meta_normalizeInstance___closed__2_once, _init_l_Lean_Meta_normalizeInstance___closed__2);
v___x_3329_ = l_Lean_MessageData_ofName(v_val_3324_);
v___x_3330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3312_, v___x_3330_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_dec_ref(v___x_3331_);
v___y_3268_ = v___x_3318_;
v___y_3269_ = v_a_3229_;
v___y_3270_ = v_a_3230_;
v___y_3271_ = v_a_3231_;
goto v___jp_3267_;
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v_val_3324_);
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3340_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3325_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3325_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v___x_3349_; 
lean_dec(v_a_3320_);
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v_inst_3224_);
v___x_3349_ = v___x_3322_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_inst_3224_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3352_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3319_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3319_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3312_, v_a_3230_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___f_3362_; lean_object* v___x_3363_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v_a_3367_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v_a_3380_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v_a_3385_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v_a_3396_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v_a_3412_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v_a_3417_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___x_3474_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref(v___x_3360_);
lean_inc_ref(v_expectedType_3225_);
v___f_3362_ = lean_alloc_closure((void*)(l_Lean_Meta_normalizeInstance___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3362_, 0, v_expectedType_3225_);
v___x_3363_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__1));
v___x_3474_ = lean_unbox(v_a_3361_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; uint8_t v___x_3476_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; 
v___x_3475_ = l_Lean_trace_profiler;
v___x_3476_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3234_, v___x_3475_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3513_; 
lean_dec_ref(v___f_3362_);
lean_dec(v_a_3361_);
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v___x_3318_);
lean_inc_ref(v_expectedType_3225_);
v___x_3513_ = l_Lean_Meta_isClass_x3f(v_expectedType_3225_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3545_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3545_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3545_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
if (lean_obj_tag(v_a_3514_) == 1)
{
lean_object* v_val_3518_; lean_object* v___x_3519_; 
lean_del_object(v___x_3516_);
v_val_3518_ = lean_ctor_get(v_a_3514_, 0);
lean_inc(v_val_3518_);
lean_dec_ref(v_a_3514_);
v___x_3519_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3312_, v_a_3230_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; uint8_t v___x_3521_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref(v___x_3519_);
v___x_3521_ = lean_unbox(v_a_3520_);
lean_dec(v_a_3520_);
if (v___x_3521_ == 0)
{
lean_dec(v_val_3518_);
v___y_3478_ = v___x_3318_;
v___y_3479_ = v_a_3229_;
v___y_3480_ = v_a_3230_;
v___y_3481_ = v_a_3231_;
goto v___jp_3477_;
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3522_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___closed__2, &l_Lean_Meta_normalizeInstance___closed__2_once, _init_l_Lean_Meta_normalizeInstance___closed__2);
v___x_3523_ = l_Lean_MessageData_ofName(v_val_3518_);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3522_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3312_, v___x_3524_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_dec_ref(v___x_3525_);
v___y_3478_ = v___x_3318_;
v___y_3479_ = v_a_3229_;
v___y_3480_ = v_a_3230_;
v___y_3481_ = v_a_3231_;
goto v___jp_3477_;
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec(v_val_3518_);
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3534_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3519_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3519_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
lean_object* v___x_3543_; 
lean_dec(v_a_3514_);
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v_inst_3224_);
v___x_3543_ = v___x_3516_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_inst_3224_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3546_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3513_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3513_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_inc_ref(v_options_3234_);
goto v___jp_3425_;
}
v___jp_3477_:
{
lean_object* v___x_3482_; 
lean_inc(v___y_3481_);
lean_inc_ref(v___y_3480_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc_ref(v_expectedType_3225_);
v___x_3482_ = l_Lean_Meta_isProp(v_expectedType_3225_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3504_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3504_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3504_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_unbox(v_a_3483_);
lean_dec(v_a_3483_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_del_object(v___x_3485_);
lean_inc(v___y_3481_);
lean_inc_ref(v___y_3480_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
v___x_3488_ = lean_whnf(v_inst_3224_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v_dummy_3490_; lean_object* v_nargs_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v___x_3488_);
v_dummy_3490_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_3491_ = l_Lean_Expr_getAppNumArgs(v_a_3489_);
lean_inc(v_nargs_3491_);
v___x_3492_ = lean_mk_array(v_nargs_3491_, v_dummy_3490_);
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_sub(v_nargs_3491_, v___x_3493_);
lean_dec(v_nargs_3491_);
lean_inc(v_a_3489_);
v___x_3495_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(v_a_3489_, v_expectedType_3225_, v___x_3476_, v_compile_3226_, v_logCompileErrors_3227_, v_hasTrace_3266_, v_a_3489_, v___x_3492_, v___x_3494_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
return v___x_3495_;
}
else
{
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec_ref(v_expectedType_3225_);
return v___x_3488_;
}
}
else
{
lean_object* v_options_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v_options_3496_ = lean_ctor_get(v___y_3480_, 2);
v___x_3497_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3498_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3496_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec_ref(v_expectedType_3225_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v_inst_3224_);
v___x_3500_ = v___x_3485_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_inst_3224_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
lean_del_object(v___x_3485_);
v___x_3502_ = lean_box(0);
v___x_3503_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_3225_, v_inst_3224_, v_hasTrace_3266_, v___x_3502_, v_hasTrace_3266_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
return v___x_3503_;
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3505_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3482_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3482_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
else
{
lean_inc_ref(v_options_3234_);
goto v___jp_3425_;
}
v___jp_3364_:
{
lean_object* v___x_3368_; double v___x_3369_; double v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3368_ = lean_io_get_num_heartbeats();
v___x_3369_ = lean_float_of_nat(v___y_3365_);
v___x_3370_ = lean_float_of_nat(v___x_3368_);
v___x_3371_ = lean_box_float(v___x_3369_);
v___x_3372_ = lean_box_float(v___x_3370_);
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3374_, 0, v_a_3367_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_unbox(v_a_3361_);
lean_dec(v_a_3361_);
v___x_3376_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(v_cls_3312_, v_hasTrace_3266_, v___x_3363_, v_options_3234_, v___x_3375_, v___y_3366_, v___f_3362_, v___x_3374_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
lean_dec_ref(v_options_3234_);
return v___x_3376_;
}
v___jp_3377_:
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_a_3380_);
v___y_3365_ = v___y_3378_;
v___y_3366_ = v___y_3379_;
v_a_3367_ = v___x_3381_;
goto v___jp_3364_;
}
v___jp_3382_:
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_a_3385_);
v___y_3365_ = v___y_3383_;
v___y_3366_ = v___y_3384_;
v_a_3367_ = v___x_3386_;
goto v___jp_3364_;
}
v___jp_3387_:
{
if (lean_obj_tag(v___y_3390_) == 0)
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v___y_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref(v___y_3390_);
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3389_;
v_a_3380_ = v_a_3391_;
goto v___jp_3377_;
}
else
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___y_3390_, 0);
lean_inc(v_a_3392_);
lean_dec_ref(v___y_3390_);
v___y_3383_ = v___y_3388_;
v___y_3384_ = v___y_3389_;
v_a_3385_ = v_a_3392_;
goto v___jp_3382_;
}
}
v___jp_3393_:
{
lean_object* v___x_3397_; double v___x_3398_; double v___x_3399_; double v___x_3400_; double v___x_3401_; double v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; lean_object* v___x_3408_; 
v___x_3397_ = lean_io_mono_nanos_now();
v___x_3398_ = lean_float_of_nat(v___y_3394_);
v___x_3399_ = lean_float_once(&l_Lean_Meta_normalizeInstance___closed__3, &l_Lean_Meta_normalizeInstance___closed__3_once, _init_l_Lean_Meta_normalizeInstance___closed__3);
v___x_3400_ = lean_float_div(v___x_3398_, v___x_3399_);
v___x_3401_ = lean_float_of_nat(v___x_3397_);
v___x_3402_ = lean_float_div(v___x_3401_, v___x_3399_);
v___x_3403_ = lean_box_float(v___x_3400_);
v___x_3404_ = lean_box_float(v___x_3402_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_a_3396_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = lean_unbox(v_a_3361_);
lean_dec(v_a_3361_);
v___x_3408_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(v_cls_3312_, v_hasTrace_3266_, v___x_3363_, v_options_3234_, v___x_3407_, v___y_3395_, v___f_3362_, v___x_3406_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
lean_dec_ref(v_options_3234_);
return v___x_3408_;
}
v___jp_3409_:
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3413_, 0, v_a_3412_);
v___y_3394_ = v___y_3410_;
v___y_3395_ = v___y_3411_;
v_a_3396_ = v___x_3413_;
goto v___jp_3393_;
}
v___jp_3414_:
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_a_3417_);
v___y_3394_ = v___y_3415_;
v___y_3395_ = v___y_3416_;
v_a_3396_ = v___x_3418_;
goto v___jp_3393_;
}
v___jp_3419_:
{
if (lean_obj_tag(v___y_3422_) == 0)
{
lean_object* v_a_3423_; 
v_a_3423_ = lean_ctor_get(v___y_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref(v___y_3422_);
v___y_3410_ = v___y_3420_;
v___y_3411_ = v___y_3421_;
v_a_3412_ = v_a_3423_;
goto v___jp_3409_;
}
else
{
lean_object* v_a_3424_; 
v_a_3424_ = lean_ctor_get(v___y_3422_, 0);
lean_inc(v_a_3424_);
lean_dec_ref(v___y_3422_);
v___y_3415_ = v___y_3420_;
v___y_3416_ = v___y_3421_;
v_a_3417_ = v_a_3424_;
goto v___jp_3414_;
}
}
v___jp_3425_:
{
lean_object* v___x_3426_; 
v___x_3426_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg(v_a_3231_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3429_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3234_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_io_mono_nanos_now();
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v___x_3318_);
lean_inc_ref(v_expectedType_3225_);
v___x_3431_ = l_Lean_Meta_isClass_x3f(v_expectedType_3225_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref(v___x_3431_);
if (lean_obj_tag(v_a_3432_) == 1)
{
lean_object* v_val_3433_; lean_object* v___x_3434_; 
v_val_3433_ = lean_ctor_get(v_a_3432_, 0);
lean_inc(v_val_3433_);
lean_dec_ref(v_a_3432_);
v___x_3434_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3312_, v_a_3230_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; uint8_t v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref(v___x_3434_);
v___x_3436_ = lean_unbox(v_a_3435_);
lean_dec(v_a_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec(v_val_3433_);
v___x_3437_ = lean_box(0);
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v___x_3318_);
v___x_3438_ = l_Lean_Meta_normalizeInstance___lam__1(v_expectedType_3225_, v_inst_3224_, v___x_3429_, v_compile_3226_, v_logCompileErrors_3227_, v_hasTrace_3266_, v___x_3437_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
v___y_3420_ = v___x_3430_;
v___y_3421_ = v_a_3427_;
v___y_3422_ = v___x_3438_;
goto v___jp_3419_;
}
else
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3439_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___closed__2, &l_Lean_Meta_normalizeInstance___closed__2_once, _init_l_Lean_Meta_normalizeInstance___closed__2);
v___x_3440_ = l_Lean_MessageData_ofName(v_val_3433_);
v___x_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3312_, v___x_3441_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3444_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref(v___x_3442_);
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v___x_3318_);
v___x_3444_ = l_Lean_Meta_normalizeInstance___lam__1(v_expectedType_3225_, v_inst_3224_, v___x_3429_, v_compile_3226_, v_logCompileErrors_3227_, v_hasTrace_3266_, v_a_3443_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
v___y_3420_ = v___x_3430_;
v___y_3421_ = v_a_3427_;
v___y_3422_ = v___x_3444_;
goto v___jp_3419_;
}
else
{
lean_object* v_a_3445_; 
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3445_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3442_);
v___y_3415_ = v___x_3430_;
v___y_3416_ = v_a_3427_;
v_a_3417_ = v_a_3445_;
goto v___jp_3414_;
}
}
}
else
{
lean_object* v_a_3446_; 
lean_dec(v_val_3433_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3446_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3446_);
lean_dec_ref(v___x_3434_);
v___y_3415_ = v___x_3430_;
v___y_3416_ = v_a_3427_;
v_a_3417_ = v_a_3446_;
goto v___jp_3414_;
}
}
else
{
lean_dec(v_a_3432_);
lean_dec_ref(v_expectedType_3225_);
v___y_3410_ = v___x_3430_;
v___y_3411_ = v_a_3427_;
v_a_3412_ = v_inst_3224_;
goto v___jp_3409_;
}
}
else
{
lean_object* v_a_3447_; 
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3447_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3431_);
v___y_3415_ = v___x_3430_;
v___y_3416_ = v_a_3427_;
v_a_3417_ = v_a_3447_;
goto v___jp_3414_;
}
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v___x_3318_);
lean_inc_ref(v_expectedType_3225_);
v___x_3449_ = l_Lean_Meta_isClass_x3f(v_expectedType_3225_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
if (lean_obj_tag(v_a_3450_) == 1)
{
lean_object* v_val_3451_; lean_object* v___x_3452_; 
v_val_3451_ = lean_ctor_get(v_a_3450_, 0);
lean_inc(v_val_3451_);
lean_dec_ref(v_a_3450_);
v___x_3452_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3312_, v_a_3230_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; uint8_t v___x_3454_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = lean_unbox(v_a_3453_);
lean_dec(v_a_3453_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_dec(v_val_3451_);
v___x_3455_ = lean_box(0);
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v___x_3318_);
v___x_3456_ = l_Lean_Meta_normalizeInstance___lam__2(v_expectedType_3225_, v_inst_3224_, v_compile_3226_, v_logCompileErrors_3227_, v___x_3429_, v___x_3455_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
v___y_3388_ = v___x_3448_;
v___y_3389_ = v_a_3427_;
v___y_3390_ = v___x_3456_;
goto v___jp_3387_;
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3457_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___closed__2, &l_Lean_Meta_normalizeInstance___closed__2_once, _init_l_Lean_Meta_normalizeInstance___closed__2);
v___x_3458_ = l_Lean_MessageData_ofName(v_val_3451_);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3312_, v___x_3459_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref(v___x_3460_);
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v___x_3318_);
v___x_3462_ = l_Lean_Meta_normalizeInstance___lam__2(v_expectedType_3225_, v_inst_3224_, v_compile_3226_, v_logCompileErrors_3227_, v___x_3429_, v_a_3461_, v___x_3318_, v_a_3229_, v_a_3230_, v_a_3231_);
v___y_3388_ = v___x_3448_;
v___y_3389_ = v_a_3427_;
v___y_3390_ = v___x_3462_;
goto v___jp_3387_;
}
else
{
lean_object* v_a_3463_; 
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3463_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3460_);
v___y_3383_ = v___x_3448_;
v___y_3384_ = v_a_3427_;
v_a_3385_ = v_a_3463_;
goto v___jp_3382_;
}
}
}
else
{
lean_object* v_a_3464_; 
lean_dec(v_val_3451_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3464_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3464_);
lean_dec_ref(v___x_3452_);
v___y_3383_ = v___x_3448_;
v___y_3384_ = v_a_3427_;
v_a_3385_ = v_a_3464_;
goto v___jp_3382_;
}
}
else
{
lean_dec(v_a_3450_);
lean_dec_ref(v_expectedType_3225_);
v___y_3378_ = v___x_3448_;
v___y_3379_ = v_a_3427_;
v_a_3380_ = v_inst_3224_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3465_; 
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3465_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3465_);
lean_dec_ref(v___x_3449_);
v___y_3383_ = v___x_3448_;
v___y_3384_ = v_a_3427_;
v_a_3385_ = v_a_3465_;
goto v___jp_3382_;
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec_ref(v___f_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v___x_3318_);
lean_dec_ref(v_options_3234_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3466_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3426_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3426_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_expectedType_3225_);
lean_dec_ref(v_inst_3224_);
v_a_3554_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3360_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3360_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(lean_object* v___x_3573_, lean_object* v_a_3574_, uint8_t v_compile_3575_, uint8_t v_logCompileErrors_3576_, lean_object* v___x_3577_, lean_object* v___x_3578_, lean_object* v_____r_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v___x_3585_; 
lean_inc(v___y_3581_);
v___x_3585_ = l_Lean_Meta_normalizeInstance(v___x_3573_, v_a_3574_, v_compile_3575_, v_logCompileErrors_3576_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref(v___x_3585_);
v___x_3587_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3577_, v_a_3586_, v___y_3581_);
lean_dec(v___y_3581_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3595_; 
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v___x_3587_, 0);
lean_dec(v_unused_3596_);
v___x_3589_ = v___x_3587_;
v_isShared_3590_ = v_isSharedCheck_3595_;
goto v_resetjp_3588_;
}
else
{
lean_dec(v___x_3587_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3595_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3578_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3591_);
v___x_3593_ = v___x_3589_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
v_a_3597_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3587_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3587_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec(v___y_3581_);
lean_dec(v___x_3577_);
v_a_3605_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3585_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3585_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1___boxed(lean_object* v___x_3613_, lean_object* v_a_3614_, lean_object* v_compile_3615_, lean_object* v_logCompileErrors_3616_, lean_object* v___x_3617_, lean_object* v___x_3618_, lean_object* v_____r_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
uint8_t v_compile_boxed_3625_; uint8_t v_logCompileErrors_boxed_3626_; lean_object* v_res_3627_; 
v_compile_boxed_3625_ = lean_unbox(v_compile_3615_);
v_logCompileErrors_boxed_3626_ = lean_unbox(v_logCompileErrors_3616_);
v_res_3627_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_3613_, v_a_3614_, v_compile_boxed_3625_, v_logCompileErrors_boxed_3626_, v___x_3617_, v___x_3618_, v_____r_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__1___boxed(lean_object* v_expectedType_3628_, lean_object* v_inst_3629_, lean_object* v___x_3630_, lean_object* v_compile_3631_, lean_object* v_logCompileErrors_3632_, lean_object* v_hasTrace_3633_, lean_object* v_____r_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
uint8_t v___x_89509__boxed_3640_; uint8_t v_compile_boxed_3641_; uint8_t v_logCompileErrors_boxed_3642_; uint8_t v_hasTrace_boxed_3643_; lean_object* v_res_3644_; 
v___x_89509__boxed_3640_ = lean_unbox(v___x_3630_);
v_compile_boxed_3641_ = lean_unbox(v_compile_3631_);
v_logCompileErrors_boxed_3642_ = lean_unbox(v_logCompileErrors_3632_);
v_hasTrace_boxed_3643_ = lean_unbox(v_hasTrace_3633_);
v_res_3644_ = l_Lean_Meta_normalizeInstance___lam__1(v_expectedType_3628_, v_inst_3629_, v___x_89509__boxed_3640_, v_compile_boxed_3641_, v_logCompileErrors_boxed_3642_, v_hasTrace_boxed_3643_, v_____r_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__2___boxed(lean_object* v_expectedType_3645_, lean_object* v_inst_3646_, lean_object* v_compile_3647_, lean_object* v_logCompileErrors_3648_, lean_object* v___x_3649_, lean_object* v_____r_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v_compile_boxed_3656_; uint8_t v_logCompileErrors_boxed_3657_; uint8_t v___x_89533__boxed_3658_; lean_object* v_res_3659_; 
v_compile_boxed_3656_ = lean_unbox(v_compile_3647_);
v_logCompileErrors_boxed_3657_ = lean_unbox(v_logCompileErrors_3648_);
v___x_89533__boxed_3658_ = lean_unbox(v___x_3649_);
v_res_3659_ = l_Lean_Meta_normalizeInstance___lam__2(v_expectedType_3645_, v_inst_3646_, v_compile_boxed_3656_, v_logCompileErrors_boxed_3657_, v___x_89533__boxed_3658_, v_____r_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___boxed(lean_object* v_a_3660_, lean_object* v_expectedType_3661_, lean_object* v___x_3662_, lean_object* v_compile_3663_, lean_object* v_logCompileErrors_3664_, lean_object* v_x_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v___x_89576__boxed_3673_; uint8_t v_compile_boxed_3674_; uint8_t v_logCompileErrors_boxed_3675_; lean_object* v_res_3676_; 
v___x_89576__boxed_3673_ = lean_unbox(v___x_3662_);
v_compile_boxed_3674_ = lean_unbox(v_compile_3663_);
v_logCompileErrors_boxed_3675_ = lean_unbox(v_logCompileErrors_3664_);
v_res_3676_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10(v_a_3660_, v_expectedType_3661_, v___x_89576__boxed_3673_, v_compile_boxed_3674_, v_logCompileErrors_boxed_3675_, v_x_3665_, v_x_3666_, v_x_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___boxed(lean_object* v_a_3677_, lean_object* v_expectedType_3678_, lean_object* v___x_3679_, lean_object* v_compile_3680_, lean_object* v_logCompileErrors_3681_, lean_object* v___x_3682_, lean_object* v_x_3683_, lean_object* v_x_3684_, lean_object* v_x_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
uint8_t v___x_89707__boxed_3691_; uint8_t v_compile_boxed_3692_; uint8_t v_logCompileErrors_boxed_3693_; uint8_t v___x_89708__boxed_3694_; lean_object* v_res_3695_; 
v___x_89707__boxed_3691_ = lean_unbox(v___x_3679_);
v_compile_boxed_3692_ = lean_unbox(v_compile_3680_);
v_logCompileErrors_boxed_3693_ = lean_unbox(v_logCompileErrors_3681_);
v___x_89708__boxed_3694_ = lean_unbox(v___x_3682_);
v_res_3695_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(v_a_3677_, v_expectedType_3678_, v___x_89707__boxed_3691_, v_compile_boxed_3692_, v_logCompileErrors_boxed_3693_, v___x_89708__boxed_3694_, v_x_3683_, v_x_3684_, v_x_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15___boxed(lean_object* v_a_3696_, lean_object* v_expectedType_3697_, lean_object* v_compile_3698_, lean_object* v_logCompileErrors_3699_, lean_object* v___x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_, lean_object* v_x_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v_compile_boxed_3709_; uint8_t v_logCompileErrors_boxed_3710_; uint8_t v___x_89848__boxed_3711_; lean_object* v_res_3712_; 
v_compile_boxed_3709_ = lean_unbox(v_compile_3698_);
v_logCompileErrors_boxed_3710_ = lean_unbox(v_logCompileErrors_3699_);
v___x_89848__boxed_3711_ = lean_unbox(v___x_3700_);
v_res_3712_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15(v_a_3696_, v_expectedType_3697_, v_compile_boxed_3709_, v_logCompileErrors_boxed_3710_, v___x_89848__boxed_3711_, v_x_3701_, v_x_3702_, v_x_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___boxed(lean_object* v_upperBound_3713_, lean_object* v_fst_3714_, lean_object* v_args_3715_, lean_object* v_compile_3716_, lean_object* v_logCompileErrors_3717_, lean_object* v___x_3718_, lean_object* v_a_3719_, lean_object* v_b_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
uint8_t v_compile_boxed_3726_; uint8_t v_logCompileErrors_boxed_3727_; uint8_t v___x_90004__boxed_3728_; lean_object* v_res_3729_; 
v_compile_boxed_3726_ = lean_unbox(v_compile_3716_);
v_logCompileErrors_boxed_3727_ = lean_unbox(v_logCompileErrors_3717_);
v___x_90004__boxed_3728_ = lean_unbox(v___x_3718_);
v_res_3729_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(v_upperBound_3713_, v_fst_3714_, v_args_3715_, v_compile_boxed_3726_, v_logCompileErrors_boxed_3727_, v___x_90004__boxed_3728_, v_a_3719_, v_b_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec_ref(v_args_3715_);
lean_dec_ref(v_fst_3714_);
lean_dec(v_upperBound_3713_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg___boxed(lean_object* v_upperBound_3730_, lean_object* v_fst_3731_, lean_object* v_args_3732_, lean_object* v___x_3733_, lean_object* v_compile_3734_, lean_object* v_logCompileErrors_3735_, lean_object* v___x_3736_, lean_object* v_a_3737_, lean_object* v_b_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
uint8_t v___x_90157__boxed_3744_; uint8_t v_compile_boxed_3745_; uint8_t v_logCompileErrors_boxed_3746_; uint8_t v___x_90158__boxed_3747_; lean_object* v_res_3748_; 
v___x_90157__boxed_3744_ = lean_unbox(v___x_3733_);
v_compile_boxed_3745_ = lean_unbox(v_compile_3734_);
v_logCompileErrors_boxed_3746_ = lean_unbox(v_logCompileErrors_3735_);
v___x_90158__boxed_3747_ = lean_unbox(v___x_3736_);
v_res_3748_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(v_upperBound_3730_, v_fst_3731_, v_args_3732_, v___x_90157__boxed_3744_, v_compile_boxed_3745_, v_logCompileErrors_boxed_3746_, v___x_90158__boxed_3747_, v_a_3737_, v_b_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec_ref(v_args_3732_);
lean_dec_ref(v_fst_3731_);
lean_dec(v_upperBound_3730_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg___boxed(lean_object* v_upperBound_3749_, lean_object* v_fst_3750_, lean_object* v_args_3751_, lean_object* v___x_3752_, lean_object* v_compile_3753_, lean_object* v_logCompileErrors_3754_, lean_object* v_a_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
uint8_t v___x_90321__boxed_3762_; uint8_t v_compile_boxed_3763_; uint8_t v_logCompileErrors_boxed_3764_; lean_object* v_res_3765_; 
v___x_90321__boxed_3762_ = lean_unbox(v___x_3752_);
v_compile_boxed_3763_ = lean_unbox(v_compile_3753_);
v_logCompileErrors_boxed_3764_ = lean_unbox(v_logCompileErrors_3754_);
v_res_3765_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(v_upperBound_3749_, v_fst_3750_, v_args_3751_, v___x_90321__boxed_3762_, v_compile_boxed_3763_, v_logCompileErrors_boxed_3764_, v_a_3755_, v_b_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec_ref(v_args_3751_);
lean_dec_ref(v_fst_3750_);
lean_dec(v_upperBound_3749_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___boxed(lean_object* v_inst_3766_, lean_object* v_expectedType_3767_, lean_object* v_compile_3768_, lean_object* v_logCompileErrors_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
uint8_t v_compile_boxed_3775_; uint8_t v_logCompileErrors_boxed_3776_; lean_object* v_res_3777_; 
v_compile_boxed_3775_ = lean_unbox(v_compile_3768_);
v_logCompileErrors_boxed_3776_ = lean_unbox(v_logCompileErrors_3769_);
v_res_3777_ = l_Lean_Meta_normalizeInstance(v_inst_3766_, v_expectedType_3767_, v_compile_boxed_3775_, v_logCompileErrors_boxed_3776_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6(size_t v_sz_3778_, size_t v_i_3779_, lean_object* v_bs_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_3778_, v_i_3779_, v_bs_3780_, v___y_3782_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___boxed(lean_object* v_sz_3787_, lean_object* v_i_3788_, lean_object* v_bs_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
size_t v_sz_boxed_3795_; size_t v_i_boxed_3796_; lean_object* v_res_3797_; 
v_sz_boxed_3795_ = lean_unbox_usize(v_sz_3787_);
lean_dec(v_sz_3787_);
v_i_boxed_3796_ = lean_unbox_usize(v_i_3788_);
lean_dec(v_i_3788_);
v_res_3797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6(v_sz_boxed_3795_, v_i_boxed_3796_, v_bs_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7(lean_object* v_upperBound_3798_, lean_object* v_fst_3799_, lean_object* v_args_3800_, uint8_t v_compile_3801_, uint8_t v_logCompileErrors_3802_, uint8_t v___x_3803_, lean_object* v_inst_3804_, lean_object* v_R_3805_, lean_object* v_a_3806_, lean_object* v_b_3807_, lean_object* v_c_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(v_upperBound_3798_, v_fst_3799_, v_args_3800_, v_compile_3801_, v_logCompileErrors_3802_, v___x_3803_, v_a_3806_, v_b_3807_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___boxed(lean_object* v_upperBound_3815_, lean_object* v_fst_3816_, lean_object* v_args_3817_, lean_object* v_compile_3818_, lean_object* v_logCompileErrors_3819_, lean_object* v___x_3820_, lean_object* v_inst_3821_, lean_object* v_R_3822_, lean_object* v_a_3823_, lean_object* v_b_3824_, lean_object* v_c_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
uint8_t v_compile_boxed_3831_; uint8_t v_logCompileErrors_boxed_3832_; uint8_t v___x_93290__boxed_3833_; lean_object* v_res_3834_; 
v_compile_boxed_3831_ = lean_unbox(v_compile_3818_);
v_logCompileErrors_boxed_3832_ = lean_unbox(v_logCompileErrors_3819_);
v___x_93290__boxed_3833_ = lean_unbox(v___x_3820_);
v_res_3834_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7(v_upperBound_3815_, v_fst_3816_, v_args_3817_, v_compile_boxed_3831_, v_logCompileErrors_boxed_3832_, v___x_93290__boxed_3833_, v_inst_3821_, v_R_3822_, v_a_3823_, v_b_3824_, v_c_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec_ref(v_args_3817_);
lean_dec_ref(v_fst_3816_);
lean_dec(v_upperBound_3815_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8(lean_object* v_00_u03b1_3835_, lean_object* v_msg_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v_msg_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___boxed(lean_object* v_00_u03b1_3843_, lean_object* v_msg_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8(v_00_u03b1_3843_, v_msg_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12(lean_object* v_upperBound_3851_, lean_object* v_fst_3852_, lean_object* v_args_3853_, uint8_t v___x_3854_, uint8_t v_compile_3855_, uint8_t v_logCompileErrors_3856_, uint8_t v___x_3857_, lean_object* v_inst_3858_, lean_object* v_R_3859_, lean_object* v_a_3860_, lean_object* v_b_3861_, lean_object* v_c_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(v_upperBound_3851_, v_fst_3852_, v_args_3853_, v___x_3854_, v_compile_3855_, v_logCompileErrors_3856_, v___x_3857_, v_a_3860_, v_b_3861_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3869_ = _args[0];
lean_object* v_fst_3870_ = _args[1];
lean_object* v_args_3871_ = _args[2];
lean_object* v___x_3872_ = _args[3];
lean_object* v_compile_3873_ = _args[4];
lean_object* v_logCompileErrors_3874_ = _args[5];
lean_object* v___x_3875_ = _args[6];
lean_object* v_inst_3876_ = _args[7];
lean_object* v_R_3877_ = _args[8];
lean_object* v_a_3878_ = _args[9];
lean_object* v_b_3879_ = _args[10];
lean_object* v_c_3880_ = _args[11];
lean_object* v___y_3881_ = _args[12];
lean_object* v___y_3882_ = _args[13];
lean_object* v___y_3883_ = _args[14];
lean_object* v___y_3884_ = _args[15];
lean_object* v___y_3885_ = _args[16];
_start:
{
uint8_t v___x_93336__boxed_3886_; uint8_t v_compile_boxed_3887_; uint8_t v_logCompileErrors_boxed_3888_; uint8_t v___x_93337__boxed_3889_; lean_object* v_res_3890_; 
v___x_93336__boxed_3886_ = lean_unbox(v___x_3872_);
v_compile_boxed_3887_ = lean_unbox(v_compile_3873_);
v_logCompileErrors_boxed_3888_ = lean_unbox(v_logCompileErrors_3874_);
v___x_93337__boxed_3889_ = lean_unbox(v___x_3875_);
v_res_3890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12(v_upperBound_3869_, v_fst_3870_, v_args_3871_, v___x_93336__boxed_3886_, v_compile_boxed_3887_, v_logCompileErrors_boxed_3888_, v___x_93337__boxed_3889_, v_inst_3876_, v_R_3877_, v_a_3878_, v_b_3879_, v_c_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec_ref(v_args_3871_);
lean_dec_ref(v_fst_3870_);
lean_dec(v_upperBound_3869_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14(lean_object* v_upperBound_3891_, lean_object* v_fst_3892_, lean_object* v_args_3893_, uint8_t v___x_3894_, uint8_t v_compile_3895_, uint8_t v_logCompileErrors_3896_, lean_object* v_inst_3897_, lean_object* v_R_3898_, lean_object* v_a_3899_, lean_object* v_b_3900_, lean_object* v_c_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(v_upperBound_3891_, v_fst_3892_, v_args_3893_, v___x_3894_, v_compile_3895_, v_logCompileErrors_3896_, v_a_3899_, v_b_3900_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___boxed(lean_object* v_upperBound_3908_, lean_object* v_fst_3909_, lean_object* v_args_3910_, lean_object* v___x_3911_, lean_object* v_compile_3912_, lean_object* v_logCompileErrors_3913_, lean_object* v_inst_3914_, lean_object* v_R_3915_, lean_object* v_a_3916_, lean_object* v_b_3917_, lean_object* v_c_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
uint8_t v___x_93368__boxed_3924_; uint8_t v_compile_boxed_3925_; uint8_t v_logCompileErrors_boxed_3926_; lean_object* v_res_3927_; 
v___x_93368__boxed_3924_ = lean_unbox(v___x_3911_);
v_compile_boxed_3925_ = lean_unbox(v_compile_3912_);
v_logCompileErrors_boxed_3926_ = lean_unbox(v_logCompileErrors_3913_);
v_res_3927_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14(v_upperBound_3908_, v_fst_3909_, v_args_3910_, v___x_93368__boxed_3924_, v_compile_boxed_3925_, v_logCompileErrors_boxed_3926_, v_inst_3914_, v_R_3915_, v_a_3916_, v_b_3917_, v_c_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec_ref(v_args_3910_);
lean_dec_ref(v_fst_3909_);
lean_dec(v_upperBound_3908_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20(lean_object* v_00_u03b1_3928_, lean_object* v_x_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v___x_3935_; 
v___x_3935_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(v_x_3929_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3936_, lean_object* v_x_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20(v_00_u03b1_3936_, v_x_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6(lean_object* v_00_u03b1_3944_, lean_object* v_constName_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(v_constName_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___boxed(lean_object* v_00_u03b1_3952_, lean_object* v_constName_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6(v_00_u03b1_3952_, v_constName_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3960_, lean_object* v_ref_3961_, lean_object* v_constName_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(v_ref_3961_, v_constName_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3969_, lean_object* v_ref_3970_, lean_object* v_constName_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8(v_00_u03b1_3969_, v_ref_3970_, v_constName_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v_ref_3970_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22(lean_object* v_00_u03b1_3978_, lean_object* v_ref_3979_, lean_object* v_msg_3980_, lean_object* v_declHint_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(v_ref_3979_, v_msg_3980_, v_declHint_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___boxed(lean_object* v_00_u03b1_3988_, lean_object* v_ref_3989_, lean_object* v_msg_3990_, lean_object* v_declHint_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22(v_00_u03b1_3988_, v_ref_3989_, v_msg_3990_, v_declHint_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v_ref_3989_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26(lean_object* v_msg_3998_, lean_object* v_declHint_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(v_msg_3998_, v_declHint_3999_, v___y_4003_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___boxed(lean_object* v_msg_4006_, lean_object* v_declHint_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26(v_msg_4006_, v_declHint_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25(lean_object* v_00_u03b1_4014_, lean_object* v_ref_4015_, lean_object* v_msg_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg(v_ref_4015_, v_msg_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___boxed(lean_object* v_00_u03b1_4023_, lean_object* v_ref_4024_, lean_object* v_msg_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25(v_00_u03b1_4023_, v_ref_4024_, v_msg_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v_ref_4024_);
return v_res_4031_;
}
}
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_InstanceNormalForm(uint8_t builtin) {
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2056448259____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_74059213____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_504867867____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_instances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_instances);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2755641687____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_data = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_data);
lean_dec_ref(res);
res = l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_InstanceNormalForm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_InstanceNormalForm(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_InstanceNormalForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_InstanceNormalForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_InstanceNormalForm(builtin);
}
#ifdef __cplusplus
}
#endif
