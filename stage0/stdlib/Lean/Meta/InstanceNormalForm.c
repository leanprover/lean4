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
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "did not reduce to constructor application, returning/wrapping as is: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "instance normal form: incorrect number of arguments for constructor application `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "instance normal form: `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__8 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__8_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not unify with the conclusion of `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__10 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__10_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_normalizeInstance___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_normalizeInstance___closed__0;
static const lean_string_object l_Lean_Meta_normalizeInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "class is "};
static const lean_object* l_Lean_Meta_normalizeInstance___closed__1 = (const lean_object*)&l_Lean_Meta_normalizeInstance___closed__1_value;
static lean_once_cell_t l_Lean_Meta_normalizeInstance___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_normalizeInstance___closed__2;
static lean_once_cell_t l_Lean_Meta_normalizeInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_normalizeInstance___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___boxed(lean_object**);
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
size_t v_x_2189__boxed_396_; size_t v_x_2190__boxed_397_; lean_object* v_res_398_; 
v_x_2189__boxed_396_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_x_2190__boxed_397_ = lean_unbox_usize(v_x_393_);
lean_dec(v_x_393_);
v_res_398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_391_, v_x_2189__boxed_396_, v_x_2190__boxed_397_, v_x_394_, v_x_395_);
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
size_t v_x_2580__boxed_599_; size_t v_x_2581__boxed_600_; lean_object* v_res_601_; 
v_x_2580__boxed_599_ = lean_unbox_usize(v_x_595_);
lean_dec(v_x_595_);
v_x_2581__boxed_600_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_res_601_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(v_00_u03b2_593_, v_x_594_, v_x_2580__boxed_599_, v_x_2581__boxed_600_, v_x_597_, v_x_598_);
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
lean_object* v_fileName_965_; lean_object* v_fileMap_966_; lean_object* v_options_967_; lean_object* v_currRecDepth_968_; lean_object* v_maxRecDepth_969_; lean_object* v_ref_970_; lean_object* v_currNamespace_971_; lean_object* v_openDecls_972_; lean_object* v_initHeartbeats_973_; lean_object* v_maxHeartbeats_974_; lean_object* v_quotContext_975_; lean_object* v_currMacroScope_976_; uint8_t v_diag_977_; lean_object* v_cancelTk_x3f_978_; uint8_t v_suppressElabErrors_979_; lean_object* v_inheritedTraceOptions_980_; lean_object* v_ref_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
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
v_ref_981_ = l_Lean_replaceRef(v_ref_958_, v_ref_970_);
lean_inc_ref(v_inheritedTraceOptions_980_);
lean_inc(v_cancelTk_x3f_978_);
lean_inc(v_currMacroScope_976_);
lean_inc(v_quotContext_975_);
lean_inc(v_maxHeartbeats_974_);
lean_inc(v_initHeartbeats_973_);
lean_inc(v_openDecls_972_);
lean_inc(v_currNamespace_971_);
lean_inc(v_maxRecDepth_969_);
lean_inc(v_currRecDepth_968_);
lean_inc_ref(v_options_967_);
lean_inc_ref(v_fileMap_966_);
lean_inc_ref(v_fileName_965_);
v___x_982_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_982_, 0, v_fileName_965_);
lean_ctor_set(v___x_982_, 1, v_fileMap_966_);
lean_ctor_set(v___x_982_, 2, v_options_967_);
lean_ctor_set(v___x_982_, 3, v_currRecDepth_968_);
lean_ctor_set(v___x_982_, 4, v_maxRecDepth_969_);
lean_ctor_set(v___x_982_, 5, v_ref_981_);
lean_ctor_set(v___x_982_, 6, v_currNamespace_971_);
lean_ctor_set(v___x_982_, 7, v_openDecls_972_);
lean_ctor_set(v___x_982_, 8, v_initHeartbeats_973_);
lean_ctor_set(v___x_982_, 9, v_maxHeartbeats_974_);
lean_ctor_set(v___x_982_, 10, v_quotContext_975_);
lean_ctor_set(v___x_982_, 11, v_currMacroScope_976_);
lean_ctor_set(v___x_982_, 12, v_cancelTk_x3f_978_);
lean_ctor_set(v___x_982_, 13, v_inheritedTraceOptions_980_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*14, v_diag_977_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*14 + 1, v_suppressElabErrors_979_);
v___x_983_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v_msg_959_, v___y_960_, v___y_961_, v___x_982_, v___y_963_);
lean_dec_ref(v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg___boxed(lean_object* v_ref_984_, lean_object* v_msg_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg(v_ref_984_, v_msg_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_ref_984_);
return v_res_991_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0(void){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__0);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_ctor_set(v___x_997_, 2, v___x_996_);
lean_ctor_set(v___x_997_, 3, v___x_995_);
lean_ctor_set(v___x_997_, 4, v___x_995_);
lean_ctor_set(v___x_997_, 5, v___x_995_);
lean_ctor_set(v___x_997_, 6, v___x_995_);
lean_ctor_set(v___x_997_, 7, v___x_995_);
lean_ctor_set(v___x_997_, 8, v___x_995_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_unsigned_to_nat(32u);
v___x_999_ = lean_mk_empty_array_with_capacity(v___x_998_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4(void){
_start:
{
size_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1001_ = ((size_t)5ULL);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_unsigned_to_nat(32u);
v___x_1004_ = lean_mk_empty_array_with_capacity(v___x_1003_);
v___x_1005_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__3);
v___x_1006_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
lean_ctor_set(v___x_1006_, 2, v___x_1002_);
lean_ctor_set(v___x_1006_, 3, v___x_1002_);
lean_ctor_set_usize(v___x_1006_, 4, v___x_1001_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = lean_box(1);
v___x_1008_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__4);
v___x_1009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__1);
v___x_1010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_1008_);
lean_ctor_set(v___x_1010_, 2, v___x_1007_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__6));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__8));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__10));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__12));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__14));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__16));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__18));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(lean_object* v_msg_1032_, lean_object* v_declHint_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v_env_1037_; uint8_t v___x_1038_; 
v___x_1036_ = lean_st_ref_get(v___y_1034_);
v_env_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_ref(v_env_1037_);
lean_dec(v___x_1036_);
v___x_1038_ = l_Lean_Name_isAnonymous(v_declHint_1033_);
if (v___x_1038_ == 0)
{
uint8_t v_isExporting_1039_; 
v_isExporting_1039_ = lean_ctor_get_uint8(v_env_1037_, sizeof(void*)*8);
if (v_isExporting_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref(v_env_1037_);
lean_dec(v_declHint_1033_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_msg_1032_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
lean_inc_ref(v_env_1037_);
v___x_1041_ = l_Lean_Environment_setExporting(v_env_1037_, v___x_1038_);
lean_inc(v_declHint_1033_);
lean_inc_ref(v___x_1041_);
v___x_1042_ = l_Lean_Environment_contains(v___x_1041_, v_declHint_1033_, v_isExporting_1039_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_env_1037_);
lean_dec(v_declHint_1033_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_msg_1032_);
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v_c_1049_; lean_object* v___x_1050_; 
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__2);
v___x_1045_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__5);
v___x_1046_ = l_Lean_Options_empty;
v___x_1047_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1041_);
lean_ctor_set(v___x_1047_, 1, v___x_1044_);
lean_ctor_set(v___x_1047_, 2, v___x_1045_);
lean_ctor_set(v___x_1047_, 3, v___x_1046_);
lean_inc(v_declHint_1033_);
v___x_1048_ = l_Lean_MessageData_ofConstName(v_declHint_1033_, v___x_1038_);
v_c_1049_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1049_, 0, v___x_1047_);
lean_ctor_set(v_c_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1037_, v_declHint_1033_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec_ref(v_env_1037_);
lean_dec(v_declHint_1033_);
v___x_1051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_c_1049_);
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__9);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_MessageData_note(v___x_1054_);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_msg_1032_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1093_; 
v_val_1058_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1060_ = v___x_1050_;
v_isShared_1061_ = v_isSharedCheck_1093_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_val_1058_);
lean_dec(v___x_1050_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1093_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_mod_1065_; uint8_t v___x_1066_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_Environment_header(v_env_1037_);
lean_dec_ref(v_env_1037_);
v___x_1064_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1063_);
v_mod_1065_ = lean_array_get(v___x_1062_, v___x_1064_, v_val_1058_);
lean_dec(v_val_1058_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l_Lean_isPrivateName(v_declHint_1033_);
lean_dec(v_declHint_1033_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__11);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v_c_1049_);
v___x_1069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__13);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_MessageData_ofName(v_mod_1065_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__15);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_MessageData_note(v___x_1074_);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_msg_1032_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1076_);
v___x_1078_ = v___x_1060_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__7);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_c_1049_);
v___x_1082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__17);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_MessageData_ofName(v_mod_1065_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___closed__19);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_MessageData_note(v___x_1087_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_msg_1032_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1089_);
v___x_1091_ = v___x_1060_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1094_; 
lean_dec_ref(v_env_1037_);
lean_dec(v_declHint_1033_);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_msg_1032_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg___boxed(lean_object* v_msg_1095_, lean_object* v_declHint_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(v_msg_1095_, v_declHint_1096_, v___y_1097_);
lean_dec(v___y_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24(lean_object* v_msg_1100_, lean_object* v_declHint_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1117_; 
v___x_1107_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(v_msg_1100_, v_declHint_1101_, v___y_1105_);
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1112_ = l_Lean_unknownIdentifierMessageTag;
v___x_1113_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1113_);
v___x_1115_ = v___x_1110_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24___boxed(lean_object* v_msg_1118_, lean_object* v_declHint_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24(v_msg_1118_, v_declHint_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(lean_object* v_ref_1126_, lean_object* v_msg_1127_, lean_object* v_declHint_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_a_1135_; lean_object* v___x_1136_; 
v___x_1134_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24(v_msg_1127_, v_declHint_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref(v___x_1134_);
v___x_1136_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg(v_ref_1126_, v_a_1135_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg___boxed(lean_object* v_ref_1137_, lean_object* v_msg_1138_, lean_object* v_declHint_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(v_ref_1137_, v_msg_1138_, v_declHint_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_ref_1137_);
return v_res_1145_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__0));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__2));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(lean_object* v_ref_1152_, lean_object* v_constName_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1159_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_1160_ = 0;
lean_inc(v_constName_1153_);
v___x_1161_ = l_Lean_MessageData_ofConstName(v_constName_1153_, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1159_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(v_ref_1152_, v___x_1164_, v_constName_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1166_, lean_object* v_constName_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(v_ref_1166_, v_constName_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v_ref_1166_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(lean_object* v_constName_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_ref_1180_; lean_object* v___x_1181_; 
v_ref_1180_ = lean_ctor_get(v___y_1177_, 5);
v___x_1181_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(v_ref_1180_, v_constName_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg___boxed(lean_object* v_constName_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(v_constName_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(lean_object* v_constName_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v_env_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = lean_st_ref_get(v___y_1193_);
v_env_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_env_1196_);
lean_dec(v___x_1195_);
v___x_1197_ = 0;
lean_inc(v_constName_1189_);
v___x_1198_ = l_Lean_Environment_find_x3f(v_env_1196_, v_constName_1189_, v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(v_constName_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1199_;
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_constName_1189_);
v_val_1200_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1198_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_dec(v___x_1198_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 0);
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_val_1200_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5___boxed(lean_object* v_constName_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(v_constName_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(lean_object* v___x_1215_, lean_object* v_a_1216_, lean_object* v_____r_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1215_, v_a_1216_, v___y_1219_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1231_; 
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1232_);
v___x_1225_ = v___x_1223_;
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
else
{
lean_dec(v___x_1223_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_box(0);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1223_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1223_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2___boxed(lean_object* v___x_1241_, lean_object* v_a_1242_, lean_object* v_____r_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_1241_, v_a_1242_, v_____r_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(lean_object* v_a_1250_, lean_object* v___x_1251_, uint8_t v_compile_1252_, uint8_t v_logCompileErrors_1253_, lean_object* v_____r_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
if (v_compile_1252_ == 0)
{
goto v___jp_1260_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_mk_empty_array_with_capacity(v___x_1279_);
lean_inc(v_a_1250_);
v___x_1281_ = lean_array_push(v___x_1280_, v_a_1250_);
v___x_1282_ = l_Lean_compileDecls(v___x_1281_, v_logCompileErrors_1253_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_dec_ref(v___x_1282_);
goto v___jp_1260_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_a_1250_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
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
v___jp_1260_:
{
lean_object* v___x_1261_; 
lean_inc_ref(v___y_1257_);
v___x_1261_ = l_Lean_enableRealizationsForConst(v_a_1250_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1261_, 0);
lean_dec(v_unused_1270_);
v___x_1263_ = v___x_1261_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v___x_1261_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1251_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v_a_1271_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1261_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1261_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0___boxed(lean_object* v_a_1291_, lean_object* v___x_1292_, lean_object* v_compile_1293_, lean_object* v_logCompileErrors_1294_, lean_object* v_____r_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
uint8_t v_compile_boxed_1301_; uint8_t v_logCompileErrors_boxed_1302_; lean_object* v_res_1303_; 
v_compile_boxed_1301_ = lean_unbox(v_compile_1293_);
v_logCompileErrors_boxed_1302_ = lean_unbox(v_logCompileErrors_1294_);
v_res_1303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_1291_, v___x_1292_, v_compile_boxed_1301_, v_logCompileErrors_boxed_1302_, v_____r_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1303_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1304_; double v___x_1305_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_float_of_nat(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(lean_object* v_cls_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_ref_1316_; lean_object* v___x_1317_; lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1362_; 
v_ref_1316_ = lean_ctor_get(v___y_1313_, 5);
v___x_1317_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4(v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1362_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1362_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v_traceState_1323_; lean_object* v_env_1324_; lean_object* v_nextMacroScope_1325_; lean_object* v_ngen_1326_; lean_object* v_auxDeclNGen_1327_; lean_object* v_cache_1328_; lean_object* v_messages_1329_; lean_object* v_infoState_1330_; lean_object* v_snapshotTasks_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1361_; 
v___x_1322_ = lean_st_ref_take(v___y_1314_);
v_traceState_1323_ = lean_ctor_get(v___x_1322_, 4);
v_env_1324_ = lean_ctor_get(v___x_1322_, 0);
v_nextMacroScope_1325_ = lean_ctor_get(v___x_1322_, 1);
v_ngen_1326_ = lean_ctor_get(v___x_1322_, 2);
v_auxDeclNGen_1327_ = lean_ctor_get(v___x_1322_, 3);
v_cache_1328_ = lean_ctor_get(v___x_1322_, 5);
v_messages_1329_ = lean_ctor_get(v___x_1322_, 6);
v_infoState_1330_ = lean_ctor_get(v___x_1322_, 7);
v_snapshotTasks_1331_ = lean_ctor_get(v___x_1322_, 8);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1333_ = v___x_1322_;
v_isShared_1334_ = v_isSharedCheck_1361_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_snapshotTasks_1331_);
lean_inc(v_infoState_1330_);
lean_inc(v_messages_1329_);
lean_inc(v_cache_1328_);
lean_inc(v_traceState_1323_);
lean_inc(v_auxDeclNGen_1327_);
lean_inc(v_ngen_1326_);
lean_inc(v_nextMacroScope_1325_);
lean_inc(v_env_1324_);
lean_dec(v___x_1322_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1361_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
uint64_t v_tid_1335_; lean_object* v_traces_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1360_; 
v_tid_1335_ = lean_ctor_get_uint64(v_traceState_1323_, sizeof(void*)*1);
v_traces_1336_ = lean_ctor_get(v_traceState_1323_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_traceState_1323_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1338_ = v_traceState_1323_;
v_isShared_1339_ = v_isSharedCheck_1360_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_traces_1336_);
lean_dec(v_traceState_1323_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1360_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; double v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0);
v___x_1342_ = 0;
v___x_1343_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__1));
v___x_1344_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1344_, 0, v_cls_1309_);
lean_ctor_set(v___x_1344_, 1, v___x_1340_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
lean_ctor_set_float(v___x_1344_, sizeof(void*)*3, v___x_1341_);
lean_ctor_set_float(v___x_1344_, sizeof(void*)*3 + 8, v___x_1341_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 16, v___x_1342_);
v___x_1345_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__2));
v___x_1346_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v_a_1318_);
lean_ctor_set(v___x_1346_, 2, v___x_1345_);
lean_inc(v_ref_1316_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_ref_1316_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = l_Lean_PersistentArray_push___redArg(v_traces_1336_, v___x_1347_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1348_);
v___x_1350_ = v___x_1338_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1348_);
lean_ctor_set_uint64(v_reuseFailAlloc_1359_, sizeof(void*)*1, v_tid_1335_);
v___x_1350_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 4, v___x_1350_);
v___x_1352_ = v___x_1333_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_env_1324_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_nextMacroScope_1325_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_ngen_1326_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_auxDeclNGen_1327_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1358_, 5, v_cache_1328_);
lean_ctor_set(v_reuseFailAlloc_1358_, 6, v_messages_1329_);
lean_ctor_set(v_reuseFailAlloc_1358_, 7, v_infoState_1330_);
lean_ctor_set(v_reuseFailAlloc_1358_, 8, v_snapshotTasks_1331_);
v___x_1352_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1353_ = lean_st_ref_set(v___y_1314_, v___x_1352_);
v___x_1354_ = lean_box(0);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1354_);
v___x_1356_ = v___x_1320_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___boxed(lean_object* v_cls_1363_, lean_object* v_msg_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_1363_, v_msg_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(lean_object* v_a_1371_, lean_object* v___x_1372_, uint8_t v___x_1373_, lean_object* v___x_1374_, lean_object* v___x_1375_, lean_object* v_____r_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Lean_Meta_mkAuxTheorem(v_a_1371_, v___x_1372_, v___x_1373_, v___x_1382_, v___x_1373_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1374_, v_a_1384_, v___y_1378_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1393_; 
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1394_);
v___x_1387_ = v___x_1385_;
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1385_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1375_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1391_ = v___x_1387_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
v_a_1395_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1385_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1385_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v___x_1374_);
v_a_1403_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1383_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1383_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3___boxed(lean_object* v_a_1411_, lean_object* v___x_1412_, lean_object* v___x_1413_, lean_object* v___x_1414_, lean_object* v___x_1415_, lean_object* v_____r_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v___x_109370__boxed_1422_; lean_object* v_res_1423_; 
v___x_109370__boxed_1422_ = lean_unbox(v___x_1413_);
v_res_1423_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_1411_, v___x_1412_, v___x_109370__boxed_1422_, v___x_1414_, v___x_1415_, v_____r_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
if (lean_obj_tag(v_a_1424_) == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = l_List_reverse___redArg(v_a_1425_);
return v___x_1426_;
}
else
{
lean_object* v_head_1427_; lean_object* v_tail_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1437_; 
v_head_1427_ = lean_ctor_get(v_a_1424_, 0);
v_tail_1428_ = lean_ctor_get(v_a_1424_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1424_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1430_ = v_a_1424_;
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_tail_1428_);
lean_inc(v_head_1427_);
lean_dec(v_a_1424_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = l_Lean_MessageData_ofExpr(v_head_1427_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v_a_1425_);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_a_1425_);
v___x_1434_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
v_a_1424_ = v_tail_1428_;
v_a_1425_ = v___x_1434_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21(size_t v_sz_1438_, size_t v_i_1439_, lean_object* v_bs_1440_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_usize_dec_lt(v_i_1439_, v_sz_1438_);
if (v___x_1441_ == 0)
{
return v_bs_1440_;
}
else
{
lean_object* v_v_1442_; lean_object* v_msg_1443_; lean_object* v___x_1444_; lean_object* v_bs_x27_1445_; size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v_v_1442_ = lean_array_uget_borrowed(v_bs_1440_, v_i_1439_);
v_msg_1443_ = lean_ctor_get(v_v_1442_, 1);
lean_inc_ref(v_msg_1443_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v_bs_x27_1445_ = lean_array_uset(v_bs_1440_, v_i_1439_, v___x_1444_);
v___x_1446_ = ((size_t)1ULL);
v___x_1447_ = lean_usize_add(v_i_1439_, v___x_1446_);
v___x_1448_ = lean_array_uset(v_bs_x27_1445_, v_i_1439_, v_msg_1443_);
v_i_1439_ = v___x_1447_;
v_bs_1440_ = v___x_1448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21___boxed(lean_object* v_sz_1450_, lean_object* v_i_1451_, lean_object* v_bs_1452_){
_start:
{
size_t v_sz_boxed_1453_; size_t v_i_boxed_1454_; lean_object* v_res_1455_; 
v_sz_boxed_1453_ = lean_unbox_usize(v_sz_1450_);
lean_dec(v_sz_1450_);
v_i_boxed_1454_ = lean_unbox_usize(v_i_1451_);
lean_dec(v_i_1451_);
v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21(v_sz_boxed_1453_, v_i_boxed_1454_, v_bs_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19(lean_object* v_oldTraces_1456_, lean_object* v_data_1457_, lean_object* v_ref_1458_, lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_fileName_1465_; lean_object* v_fileMap_1466_; lean_object* v_options_1467_; lean_object* v_currRecDepth_1468_; lean_object* v_maxRecDepth_1469_; lean_object* v_ref_1470_; lean_object* v_currNamespace_1471_; lean_object* v_openDecls_1472_; lean_object* v_initHeartbeats_1473_; lean_object* v_maxHeartbeats_1474_; lean_object* v_quotContext_1475_; lean_object* v_currMacroScope_1476_; uint8_t v_diag_1477_; lean_object* v_cancelTk_x3f_1478_; uint8_t v_suppressElabErrors_1479_; lean_object* v_inheritedTraceOptions_1480_; lean_object* v___x_1481_; lean_object* v_traceState_1482_; lean_object* v_traces_1483_; lean_object* v_ref_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; size_t v_sz_1487_; size_t v___x_1488_; lean_object* v___x_1489_; lean_object* v_msg_1490_; lean_object* v___x_1491_; lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1529_; 
v_fileName_1465_ = lean_ctor_get(v___y_1462_, 0);
v_fileMap_1466_ = lean_ctor_get(v___y_1462_, 1);
v_options_1467_ = lean_ctor_get(v___y_1462_, 2);
v_currRecDepth_1468_ = lean_ctor_get(v___y_1462_, 3);
v_maxRecDepth_1469_ = lean_ctor_get(v___y_1462_, 4);
v_ref_1470_ = lean_ctor_get(v___y_1462_, 5);
v_currNamespace_1471_ = lean_ctor_get(v___y_1462_, 6);
v_openDecls_1472_ = lean_ctor_get(v___y_1462_, 7);
v_initHeartbeats_1473_ = lean_ctor_get(v___y_1462_, 8);
v_maxHeartbeats_1474_ = lean_ctor_get(v___y_1462_, 9);
v_quotContext_1475_ = lean_ctor_get(v___y_1462_, 10);
v_currMacroScope_1476_ = lean_ctor_get(v___y_1462_, 11);
v_diag_1477_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*14);
v_cancelTk_x3f_1478_ = lean_ctor_get(v___y_1462_, 12);
v_suppressElabErrors_1479_ = lean_ctor_get_uint8(v___y_1462_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1480_ = lean_ctor_get(v___y_1462_, 13);
v___x_1481_ = lean_st_ref_get(v___y_1463_);
v_traceState_1482_ = lean_ctor_get(v___x_1481_, 4);
lean_inc_ref(v_traceState_1482_);
lean_dec(v___x_1481_);
v_traces_1483_ = lean_ctor_get(v_traceState_1482_, 0);
lean_inc_ref(v_traces_1483_);
lean_dec_ref(v_traceState_1482_);
v_ref_1484_ = l_Lean_replaceRef(v_ref_1458_, v_ref_1470_);
lean_inc_ref(v_inheritedTraceOptions_1480_);
lean_inc(v_cancelTk_x3f_1478_);
lean_inc(v_currMacroScope_1476_);
lean_inc(v_quotContext_1475_);
lean_inc(v_maxHeartbeats_1474_);
lean_inc(v_initHeartbeats_1473_);
lean_inc(v_openDecls_1472_);
lean_inc(v_currNamespace_1471_);
lean_inc(v_maxRecDepth_1469_);
lean_inc(v_currRecDepth_1468_);
lean_inc_ref(v_options_1467_);
lean_inc_ref(v_fileMap_1466_);
lean_inc_ref(v_fileName_1465_);
v___x_1485_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1485_, 0, v_fileName_1465_);
lean_ctor_set(v___x_1485_, 1, v_fileMap_1466_);
lean_ctor_set(v___x_1485_, 2, v_options_1467_);
lean_ctor_set(v___x_1485_, 3, v_currRecDepth_1468_);
lean_ctor_set(v___x_1485_, 4, v_maxRecDepth_1469_);
lean_ctor_set(v___x_1485_, 5, v_ref_1484_);
lean_ctor_set(v___x_1485_, 6, v_currNamespace_1471_);
lean_ctor_set(v___x_1485_, 7, v_openDecls_1472_);
lean_ctor_set(v___x_1485_, 8, v_initHeartbeats_1473_);
lean_ctor_set(v___x_1485_, 9, v_maxHeartbeats_1474_);
lean_ctor_set(v___x_1485_, 10, v_quotContext_1475_);
lean_ctor_set(v___x_1485_, 11, v_currMacroScope_1476_);
lean_ctor_set(v___x_1485_, 12, v_cancelTk_x3f_1478_);
lean_ctor_set(v___x_1485_, 13, v_inheritedTraceOptions_1480_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*14, v_diag_1477_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*14 + 1, v_suppressElabErrors_1479_);
v___x_1486_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1483_);
lean_dec_ref(v_traces_1483_);
v_sz_1487_ = lean_array_size(v___x_1486_);
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19_spec__21(v_sz_1487_, v___x_1488_, v___x_1486_);
v_msg_1490_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1490_, 0, v_data_1457_);
lean_ctor_set(v_msg_1490_, 1, v_msg_1459_);
lean_ctor_set(v_msg_1490_, 2, v___x_1489_);
v___x_1491_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4_spec__4(v_msg_1490_, v___y_1460_, v___y_1461_, v___x_1485_, v___y_1463_);
lean_dec_ref(v___x_1485_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1529_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1529_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v_traceState_1497_; lean_object* v_env_1498_; lean_object* v_nextMacroScope_1499_; lean_object* v_ngen_1500_; lean_object* v_auxDeclNGen_1501_; lean_object* v_cache_1502_; lean_object* v_messages_1503_; lean_object* v_infoState_1504_; lean_object* v_snapshotTasks_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1528_; 
v___x_1496_ = lean_st_ref_take(v___y_1463_);
v_traceState_1497_ = lean_ctor_get(v___x_1496_, 4);
v_env_1498_ = lean_ctor_get(v___x_1496_, 0);
v_nextMacroScope_1499_ = lean_ctor_get(v___x_1496_, 1);
v_ngen_1500_ = lean_ctor_get(v___x_1496_, 2);
v_auxDeclNGen_1501_ = lean_ctor_get(v___x_1496_, 3);
v_cache_1502_ = lean_ctor_get(v___x_1496_, 5);
v_messages_1503_ = lean_ctor_get(v___x_1496_, 6);
v_infoState_1504_ = lean_ctor_get(v___x_1496_, 7);
v_snapshotTasks_1505_ = lean_ctor_get(v___x_1496_, 8);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1507_ = v___x_1496_;
v_isShared_1508_ = v_isSharedCheck_1528_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_snapshotTasks_1505_);
lean_inc(v_infoState_1504_);
lean_inc(v_messages_1503_);
lean_inc(v_cache_1502_);
lean_inc(v_traceState_1497_);
lean_inc(v_auxDeclNGen_1501_);
lean_inc(v_ngen_1500_);
lean_inc(v_nextMacroScope_1499_);
lean_inc(v_env_1498_);
lean_dec(v___x_1496_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1528_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
uint64_t v_tid_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1526_; 
v_tid_1509_ = lean_ctor_get_uint64(v_traceState_1497_, sizeof(void*)*1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_traceState_1497_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_traceState_1497_, 0);
lean_dec(v_unused_1527_);
v___x_1511_ = v_traceState_1497_;
v_isShared_1512_ = v_isSharedCheck_1526_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v_traceState_1497_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1526_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_ref_1458_);
lean_ctor_set(v___x_1513_, 1, v_a_1492_);
v___x_1514_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1456_, v___x_1513_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1514_);
v___x_1516_ = v___x_1511_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1514_);
lean_ctor_set_uint64(v_reuseFailAlloc_1525_, sizeof(void*)*1, v_tid_1509_);
v___x_1516_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 4, v___x_1516_);
v___x_1518_ = v___x_1507_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_env_1498_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_nextMacroScope_1499_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_ngen_1500_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_auxDeclNGen_1501_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1524_, 5, v_cache_1502_);
lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_messages_1503_);
lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_infoState_1504_);
lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_snapshotTasks_1505_);
v___x_1518_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1519_ = lean_st_ref_set(v___y_1463_, v___x_1518_);
v___x_1520_ = lean_box(0);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1520_);
v___x_1522_ = v___x_1494_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19___boxed(lean_object* v_oldTraces_1530_, lean_object* v_data_1531_, lean_object* v_ref_1532_, lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19(v_oldTraces_1530_, v_data_1531_, v_ref_1532_, v_msg_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(lean_object* v_x_1540_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v_x_1540_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_x_1540_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v_x_1540_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v_x_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 1);
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v_x_1540_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_x_1540_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v_x_1540_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v_x_1540_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 0);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg___boxed(lean_object* v_x_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(v_x_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(lean_object* v_opts_1561_, lean_object* v_opt_1562_){
_start:
{
lean_object* v_name_1563_; lean_object* v_defValue_1564_; lean_object* v_map_1565_; lean_object* v___x_1566_; 
v_name_1563_ = lean_ctor_get(v_opt_1562_, 0);
v_defValue_1564_ = lean_ctor_get(v_opt_1562_, 1);
v_map_1565_ = lean_ctor_get(v_opts_1561_, 0);
v___x_1566_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1565_, v_name_1563_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_inc(v_defValue_1564_);
return v_defValue_1564_;
}
else
{
lean_object* v_val_1567_; 
v_val_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1567_);
lean_dec_ref(v___x_1566_);
if (lean_obj_tag(v_val_1567_) == 3)
{
lean_object* v_v_1568_; 
v_v_1568_ = lean_ctor_get(v_val_1567_, 0);
lean_inc(v_v_1568_);
lean_dec_ref(v_val_1567_);
return v_v_1568_;
}
else
{
lean_dec(v_val_1567_);
lean_inc(v_defValue_1564_);
return v_defValue_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21___boxed(lean_object* v_opts_1569_, lean_object* v_opt_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(v_opts_1569_, v_opt_1570_);
lean_dec_ref(v_opt_1570_);
lean_dec_ref(v_opts_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18(lean_object* v_e_1572_){
_start:
{
if (lean_obj_tag(v_e_1572_) == 0)
{
uint8_t v___x_1573_; 
v___x_1573_ = 2;
return v___x_1573_;
}
else
{
uint8_t v___x_1574_; 
v___x_1574_ = 0;
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18___boxed(lean_object* v_e_1575_){
_start:
{
uint8_t v_res_1576_; lean_object* v_r_1577_; 
v_res_1576_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18(v_e_1575_);
lean_dec_ref(v_e_1575_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__0));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__2));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4(void){
_start:
{
lean_object* v___x_1584_; double v___x_1585_; 
v___x_1584_ = lean_unsigned_to_nat(1000u);
v___x_1585_ = lean_float_of_nat(v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(lean_object* v_cls_1586_, uint8_t v_collapsed_1587_, lean_object* v_tag_1588_, lean_object* v_opts_1589_, uint8_t v_clsEnabled_1590_, lean_object* v_oldTraces_1591_, lean_object* v_msg_1592_, lean_object* v_resStartStop_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1698_; 
v_fst_1599_ = lean_ctor_get(v_resStartStop_1593_, 0);
v_snd_1600_ = lean_ctor_get(v_resStartStop_1593_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_resStartStop_1593_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1602_ = v_resStartStop_1593_;
v_isShared_1603_ = v_isSharedCheck_1698_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_snd_1600_);
lean_inc(v_fst_1599_);
lean_dec(v_resStartStop_1593_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1698_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v_data_1607_; lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1697_; 
v_fst_1618_ = lean_ctor_get(v_snd_1600_, 0);
v_snd_1619_ = lean_ctor_get(v_snd_1600_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_snd_1600_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1621_ = v_snd_1600_;
v_isShared_1622_ = v_isSharedCheck_1697_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_snd_1619_);
lean_inc(v_fst_1618_);
lean_dec(v_snd_1600_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1697_;
goto v_resetjp_1620_;
}
v___jp_1604_:
{
lean_object* v___x_1608_; 
lean_inc(v___y_1606_);
v___x_1608_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__19(v_oldTraces_1591_, v_data_1607_, v___y_1606_, v___y_1605_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref(v___x_1608_);
v___x_1609_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(v_fst_1599_);
return v___x_1609_;
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_fst_1599_);
v_a_1610_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1608_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1608_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; uint8_t v___x_1624_; lean_object* v___y_1626_; lean_object* v_a_1627_; uint8_t v___y_1651_; double v___y_1682_; 
v___x_1623_ = l_Lean_trace_profiler;
v___x_1624_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_opts_1589_, v___x_1623_);
if (v___x_1624_ == 0)
{
v___y_1651_ = v___x_1624_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1688_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_opts_1589_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; double v___x_1691_; double v___x_1692_; double v___x_1693_; 
v___x_1689_ = l_Lean_trace_profiler_threshold;
v___x_1690_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(v_opts_1589_, v___x_1689_);
v___x_1691_ = lean_float_of_nat(v___x_1690_);
v___x_1692_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__4);
v___x_1693_ = lean_float_div(v___x_1691_, v___x_1692_);
v___y_1682_ = v___x_1693_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; double v___x_1696_; 
v___x_1694_ = l_Lean_trace_profiler_threshold;
v___x_1695_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__21(v_opts_1589_, v___x_1694_);
v___x_1696_ = lean_float_of_nat(v___x_1695_);
v___y_1682_ = v___x_1696_;
goto v___jp_1681_;
}
}
v___jp_1625_:
{
uint8_t v_result_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v_result_1628_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__18(v_fst_1599_);
v___x_1629_ = l_Lean_TraceResult_toEmoji(v_result_1628_);
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
v___x_1631_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__1);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 7);
lean_ctor_set(v___x_1621_, 1, v___x_1631_);
lean_ctor_set(v___x_1621_, 0, v___x_1630_);
v___x_1633_ = v___x_1621_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v_m_1635_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 7);
lean_ctor_set(v___x_1602_, 1, v_a_1627_);
lean_ctor_set(v___x_1602_, 0, v___x_1633_);
v_m_1635_ = v___x_1602_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_a_1627_);
v_m_1635_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; double v___x_1638_; lean_object* v_data_1639_; 
v___x_1636_ = lean_box(v_result_1628_);
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
v___x_1638_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__0);
lean_inc_ref(v_tag_1588_);
lean_inc_ref(v___x_1637_);
lean_inc(v_cls_1586_);
v_data_1639_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1639_, 0, v_cls_1586_);
lean_ctor_set(v_data_1639_, 1, v___x_1637_);
lean_ctor_set(v_data_1639_, 2, v_tag_1588_);
lean_ctor_set_float(v_data_1639_, sizeof(void*)*3, v___x_1638_);
lean_ctor_set_float(v_data_1639_, sizeof(void*)*3 + 8, v___x_1638_);
lean_ctor_set_uint8(v_data_1639_, sizeof(void*)*3 + 16, v_collapsed_1587_);
if (v___x_1624_ == 0)
{
lean_dec_ref(v___x_1637_);
lean_dec(v_snd_1619_);
lean_dec(v_fst_1618_);
lean_dec_ref(v_tag_1588_);
lean_dec(v_cls_1586_);
v___y_1605_ = v_m_1635_;
v___y_1606_ = v___y_1626_;
v_data_1607_ = v_data_1639_;
goto v___jp_1604_;
}
else
{
lean_object* v_data_1640_; double v___x_1641_; double v___x_1642_; 
lean_dec_ref(v_data_1639_);
v_data_1640_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1640_, 0, v_cls_1586_);
lean_ctor_set(v_data_1640_, 1, v___x_1637_);
lean_ctor_set(v_data_1640_, 2, v_tag_1588_);
v___x_1641_ = lean_unbox_float(v_fst_1618_);
lean_dec(v_fst_1618_);
lean_ctor_set_float(v_data_1640_, sizeof(void*)*3, v___x_1641_);
v___x_1642_ = lean_unbox_float(v_snd_1619_);
lean_dec(v_snd_1619_);
lean_ctor_set_float(v_data_1640_, sizeof(void*)*3 + 8, v___x_1642_);
lean_ctor_set_uint8(v_data_1640_, sizeof(void*)*3 + 16, v_collapsed_1587_);
v___y_1605_ = v_m_1635_;
v___y_1606_ = v___y_1626_;
v_data_1607_ = v_data_1640_;
goto v___jp_1604_;
}
}
}
}
v___jp_1645_:
{
lean_object* v_ref_1646_; lean_object* v___x_1647_; 
v_ref_1646_ = lean_ctor_get(v___y_1596_, 5);
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1596_);
lean_inc(v___y_1595_);
lean_inc_ref(v___y_1594_);
lean_inc(v_fst_1599_);
v___x_1647_ = lean_apply_6(v_msg_1592_, v_fst_1599_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, lean_box(0));
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref(v___x_1647_);
v___y_1626_ = v_ref_1646_;
v_a_1627_ = v_a_1648_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1649_; 
lean_dec_ref(v___x_1647_);
v___x_1649_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___closed__3);
v___y_1626_ = v_ref_1646_;
v_a_1627_ = v___x_1649_;
goto v___jp_1625_;
}
}
v___jp_1650_:
{
if (v_clsEnabled_1590_ == 0)
{
if (v___y_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v_traceState_1653_; lean_object* v_env_1654_; lean_object* v_nextMacroScope_1655_; lean_object* v_ngen_1656_; lean_object* v_auxDeclNGen_1657_; lean_object* v_cache_1658_; lean_object* v_messages_1659_; lean_object* v_infoState_1660_; lean_object* v_snapshotTasks_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1680_; 
lean_del_object(v___x_1621_);
lean_dec(v_snd_1619_);
lean_dec(v_fst_1618_);
lean_del_object(v___x_1602_);
lean_dec_ref(v_msg_1592_);
lean_dec_ref(v_tag_1588_);
lean_dec(v_cls_1586_);
v___x_1652_ = lean_st_ref_take(v___y_1597_);
v_traceState_1653_ = lean_ctor_get(v___x_1652_, 4);
v_env_1654_ = lean_ctor_get(v___x_1652_, 0);
v_nextMacroScope_1655_ = lean_ctor_get(v___x_1652_, 1);
v_ngen_1656_ = lean_ctor_get(v___x_1652_, 2);
v_auxDeclNGen_1657_ = lean_ctor_get(v___x_1652_, 3);
v_cache_1658_ = lean_ctor_get(v___x_1652_, 5);
v_messages_1659_ = lean_ctor_get(v___x_1652_, 6);
v_infoState_1660_ = lean_ctor_get(v___x_1652_, 7);
v_snapshotTasks_1661_ = lean_ctor_get(v___x_1652_, 8);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1663_ = v___x_1652_;
v_isShared_1664_ = v_isSharedCheck_1680_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_snapshotTasks_1661_);
lean_inc(v_infoState_1660_);
lean_inc(v_messages_1659_);
lean_inc(v_cache_1658_);
lean_inc(v_traceState_1653_);
lean_inc(v_auxDeclNGen_1657_);
lean_inc(v_ngen_1656_);
lean_inc(v_nextMacroScope_1655_);
lean_inc(v_env_1654_);
lean_dec(v___x_1652_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1680_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
uint64_t v_tid_1665_; lean_object* v_traces_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1679_; 
v_tid_1665_ = lean_ctor_get_uint64(v_traceState_1653_, sizeof(void*)*1);
v_traces_1666_ = lean_ctor_get(v_traceState_1653_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_traceState_1653_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1668_ = v_traceState_1653_;
v_isShared_1669_ = v_isSharedCheck_1679_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_traces_1666_);
lean_dec(v_traceState_1653_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1679_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1591_, v_traces_1666_);
lean_dec_ref(v_traces_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1670_);
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1670_);
lean_ctor_set_uint64(v_reuseFailAlloc_1678_, sizeof(void*)*1, v_tid_1665_);
v___x_1672_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 4, v___x_1672_);
v___x_1674_ = v___x_1663_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_env_1654_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_nextMacroScope_1655_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_ngen_1656_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_auxDeclNGen_1657_);
lean_ctor_set(v_reuseFailAlloc_1677_, 4, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1677_, 5, v_cache_1658_);
lean_ctor_set(v_reuseFailAlloc_1677_, 6, v_messages_1659_);
lean_ctor_set(v_reuseFailAlloc_1677_, 7, v_infoState_1660_);
lean_ctor_set(v_reuseFailAlloc_1677_, 8, v_snapshotTasks_1661_);
v___x_1674_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_st_ref_set(v___y_1597_, v___x_1674_);
v___x_1676_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(v_fst_1599_);
return v___x_1676_;
}
}
}
}
}
else
{
goto v___jp_1645_;
}
}
else
{
goto v___jp_1645_;
}
}
v___jp_1681_:
{
double v___x_1683_; double v___x_1684_; double v___x_1685_; uint8_t v___x_1686_; 
v___x_1683_ = lean_unbox_float(v_snd_1619_);
v___x_1684_ = lean_unbox_float(v_fst_1618_);
v___x_1685_ = lean_float_sub(v___x_1683_, v___x_1684_);
v___x_1686_ = lean_float_decLt(v___y_1682_, v___x_1685_);
v___y_1651_ = v___x_1686_;
goto v___jp_1650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16___boxed(lean_object* v_cls_1699_, lean_object* v_collapsed_1700_, lean_object* v_tag_1701_, lean_object* v_opts_1702_, lean_object* v_clsEnabled_1703_, lean_object* v_oldTraces_1704_, lean_object* v_msg_1705_, lean_object* v_resStartStop_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v_collapsed_boxed_1712_; uint8_t v_clsEnabled_boxed_1713_; lean_object* v_res_1714_; 
v_collapsed_boxed_1712_ = lean_unbox(v_collapsed_1700_);
v_clsEnabled_boxed_1713_ = lean_unbox(v_clsEnabled_1703_);
v_res_1714_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(v_cls_1699_, v_collapsed_boxed_1712_, v_tag_1701_, v_opts_1702_, v_clsEnabled_boxed_1713_, v_oldTraces_1704_, v_msg_1705_, v_resStartStop_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec_ref(v_opts_1702_);
return v_res_1714_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__2));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__0));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__2));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__4));
v___x_1729_ = l_Lean_stringToMessageData(v___x_1728_);
return v___x_1729_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__6));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__8));
v___x_1735_ = l_Lean_stringToMessageData(v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(lean_object* v_upperBound_1736_, lean_object* v_fst_1737_, lean_object* v_args_1738_, uint8_t v_compile_1739_, uint8_t v_logCompileErrors_1740_, uint8_t v_isMeta_1741_, uint8_t v___x_1742_, lean_object* v_a_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_a_1751_; lean_object* v___y_1756_; uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_lt(v_a_1743_, v_upperBound_1736_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
lean_dec(v_a_1743_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_b_1744_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_array_fget_borrowed(v_fst_1737_, v_a_1743_);
v___x_1778_ = l_Lean_Expr_mvarId_x21(v___x_1777_);
lean_inc(v___x_1778_);
v___x_1779_ = l_Lean_MVarId_getDecl(v___x_1778_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v_type_1781_; lean_object* v___x_1782_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
v_type_1781_ = lean_ctor_get(v_a_1780_, 2);
lean_inc_ref(v_type_1781_);
lean_dec(v_a_1780_);
v___x_1782_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_1781_, v___y_1746_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
lean_inc(v_a_1783_);
v___x_1784_ = l_Lean_Meta_isProp(v_a_1783_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; lean_object* v_cls_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___x_1784_);
v___x_1786_ = lean_box(0);
v_cls_1787_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_1788_ = lean_array_fget_borrowed(v_args_1738_, v_a_1743_);
v___x_1789_ = lean_unbox(v_a_1785_);
lean_dec(v_a_1785_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; 
lean_inc(v_a_1783_);
v___x_1790_ = l_Lean_Meta_isClass_x3f(v_a_1783_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1921_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1921_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1921_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
if (lean_obj_tag(v_a_1791_) == 0)
{
lean_object* v_options_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
lean_del_object(v___x_1793_);
v_options_1795_ = lean_ctor_get(v___y_1747_, 2);
v___x_1796_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_1797_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
lean_dec(v_a_1783_);
lean_inc(v___x_1788_);
v___x_1798_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1778_, v___x_1788_, v___y_1746_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_dec_ref(v___x_1798_);
v_a_1751_ = v___x_1786_;
goto v___jp_1750_;
}
else
{
lean_dec(v_a_1743_);
return v___x_1798_;
}
}
else
{
lean_object* v___x_1799_; 
lean_inc(v___y_1748_);
lean_inc_ref(v___y_1747_);
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1745_);
lean_inc(v___x_1788_);
v___x_1799_ = lean_infer_type(v___x_1788_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v___x_1799_);
lean_inc(v_a_1783_);
v___x_1801_ = l_Lean_Meta_isExprDefEq(v_a_1783_, v_a_1800_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; uint8_t v___x_1803_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = lean_unbox(v_a_1802_);
lean_dec(v_a_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1));
v___x_1805_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_1804_, v___y_1748_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1805_);
lean_inc(v___x_1788_);
lean_inc(v_a_1806_);
v___x_1807_ = l_Lean_Meta_mkAuxDefinition(v_a_1806_, v_a_1783_, v___x_1788_, v___x_1742_, v___x_1742_, v___x_1775_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1778_, v_a_1808_, v___y_1746_);
if (lean_obj_tag(v___x_1809_) == 0)
{
uint8_t v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v___x_1809_);
v___x_1810_ = 0;
lean_inc(v_a_1806_);
v___x_1811_ = l_Lean_Meta_setInlineAttribute(v_a_1806_, v___x_1810_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_dec_ref(v___x_1811_);
if (v_isMeta_1741_ == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_1806_, v___x_1786_, v_compile_1739_, v_logCompileErrors_1740_, v___x_1786_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v___y_1756_ = v___x_1812_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1813_; lean_object* v_env_1814_; lean_object* v_nextMacroScope_1815_; lean_object* v_ngen_1816_; lean_object* v_auxDeclNGen_1817_; lean_object* v_traceState_1818_; lean_object* v_messages_1819_; lean_object* v_infoState_1820_; lean_object* v_snapshotTasks_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1847_; 
v___x_1813_ = lean_st_ref_take(v___y_1748_);
v_env_1814_ = lean_ctor_get(v___x_1813_, 0);
v_nextMacroScope_1815_ = lean_ctor_get(v___x_1813_, 1);
v_ngen_1816_ = lean_ctor_get(v___x_1813_, 2);
v_auxDeclNGen_1817_ = lean_ctor_get(v___x_1813_, 3);
v_traceState_1818_ = lean_ctor_get(v___x_1813_, 4);
v_messages_1819_ = lean_ctor_get(v___x_1813_, 6);
v_infoState_1820_ = lean_ctor_get(v___x_1813_, 7);
v_snapshotTasks_1821_ = lean_ctor_get(v___x_1813_, 8);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v___x_1813_, 5);
lean_dec(v_unused_1848_);
v___x_1823_ = v___x_1813_;
v_isShared_1824_ = v_isSharedCheck_1847_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_snapshotTasks_1821_);
lean_inc(v_infoState_1820_);
lean_inc(v_messages_1819_);
lean_inc(v_traceState_1818_);
lean_inc(v_auxDeclNGen_1817_);
lean_inc(v_ngen_1816_);
lean_inc(v_nextMacroScope_1815_);
lean_inc(v_env_1814_);
lean_dec(v___x_1813_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1847_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_inc(v_a_1806_);
v___x_1825_ = l_Lean_markMeta(v_env_1814_, v_a_1806_);
v___x_1826_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 5, v___x_1826_);
lean_ctor_set(v___x_1823_, 0, v___x_1825_);
v___x_1828_ = v___x_1823_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_nextMacroScope_1815_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_ngen_1816_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_auxDeclNGen_1817_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_traceState_1818_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1846_, 6, v_messages_1819_);
lean_ctor_set(v_reuseFailAlloc_1846_, 7, v_infoState_1820_);
lean_ctor_set(v_reuseFailAlloc_1846_, 8, v_snapshotTasks_1821_);
v___x_1828_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v_mctx_1831_; lean_object* v_zetaDeltaFVarIds_1832_; lean_object* v_postponed_1833_; lean_object* v_diag_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1844_; 
v___x_1829_ = lean_st_ref_set(v___y_1748_, v___x_1828_);
v___x_1830_ = lean_st_ref_take(v___y_1746_);
v_mctx_1831_ = lean_ctor_get(v___x_1830_, 0);
v_zetaDeltaFVarIds_1832_ = lean_ctor_get(v___x_1830_, 2);
v_postponed_1833_ = lean_ctor_get(v___x_1830_, 3);
v_diag_1834_ = lean_ctor_get(v___x_1830_, 4);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; 
v_unused_1845_ = lean_ctor_get(v___x_1830_, 1);
lean_dec(v_unused_1845_);
v___x_1836_ = v___x_1830_;
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_diag_1834_);
lean_inc(v_postponed_1833_);
lean_inc(v_zetaDeltaFVarIds_1832_);
lean_inc(v_mctx_1831_);
lean_dec(v___x_1830_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 1, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_mctx_1831_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_zetaDeltaFVarIds_1832_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_postponed_1833_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_diag_1834_);
v___x_1840_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_st_ref_set(v___y_1746_, v___x_1840_);
v___x_1842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_1806_, v___x_1786_, v_compile_1739_, v_logCompileErrors_1740_, v___x_1786_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v___y_1756_ = v___x_1842_;
goto v___jp_1755_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1806_);
lean_dec(v_a_1743_);
return v___x_1811_;
}
}
else
{
lean_dec(v_a_1806_);
lean_dec(v_a_1743_);
return v___x_1809_;
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1806_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1849_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1807_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1807_);
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
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1857_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1805_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1805_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v___x_1865_; 
lean_dec(v_a_1783_);
lean_inc(v___x_1788_);
v___x_1865_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1778_, v___x_1788_, v___y_1746_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_dec_ref(v___x_1865_);
v_a_1751_ = v___x_1786_;
goto v___jp_1750_;
}
else
{
lean_dec(v_a_1743_);
return v___x_1865_;
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1866_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1801_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1801_);
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
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1874_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1799_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1799_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
else
{
lean_object* v_options_1882_; lean_object* v_a_1884_; lean_object* v___y_1887_; uint8_t v___y_1888_; lean_object* v_a_1893_; lean_object* v___y_1897_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
lean_dec_ref(v_a_1791_);
v_options_1882_ = lean_ctor_get(v___y_1747_, 2);
v___x_1901_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_1902_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_1882_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_del_object(v___x_1793_);
lean_inc(v___x_1788_);
v___x_1903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_1788_, v_a_1783_, v_compile_1739_, v_logCompileErrors_1740_, v_isMeta_1741_, v___x_1778_, v___x_1786_, v___x_1786_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v___y_1756_ = v___x_1903_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_box(0);
lean_inc(v_a_1783_);
v___x_1905_ = l_Lean_Meta_trySynthInstance(v_a_1783_, v___x_1904_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
if (lean_obj_tag(v_a_1906_) == 1)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v_a_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v_a_1906_);
v___x_1908_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_1787_, v___y_1747_);
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
lean_object* v___x_1911_; 
lean_inc(v___x_1778_);
v___x_1911_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_1778_, v_a_1907_, v___x_1786_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v___y_1897_ = v___x_1911_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1912_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1);
lean_inc(v_a_1907_);
v___x_1913_ = l_Lean_MessageData_ofExpr(v_a_1907_);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_1787_, v___x_1914_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
lean_inc(v___x_1778_);
v___x_1917_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_1778_, v_a_1907_, v_a_1916_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v___y_1897_ = v___x_1917_;
goto v___jp_1896_;
}
else
{
lean_object* v_a_1918_; 
lean_dec(v_a_1907_);
v_a_1918_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1915_);
v_a_1893_ = v_a_1918_;
goto v___jp_1892_;
}
}
}
else
{
lean_object* v_a_1919_; 
lean_dec(v_a_1907_);
v_a_1919_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1908_);
v_a_1893_ = v_a_1919_;
goto v___jp_1892_;
}
}
else
{
lean_dec(v_a_1906_);
lean_del_object(v___x_1793_);
v_a_1884_ = v___x_1786_;
goto v___jp_1883_;
}
}
else
{
lean_object* v_a_1920_; 
v_a_1920_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1920_);
lean_dec_ref(v___x_1905_);
v_a_1893_ = v_a_1920_;
goto v___jp_1892_;
}
}
v___jp_1883_:
{
lean_object* v___x_1885_; 
lean_inc(v___x_1788_);
v___x_1885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_1788_, v_a_1783_, v_compile_1739_, v_logCompileErrors_1740_, v_isMeta_1741_, v___x_1778_, v___x_1786_, v_a_1884_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v___y_1756_ = v___x_1885_;
goto v___jp_1755_;
}
v___jp_1886_:
{
if (v___y_1888_ == 0)
{
lean_dec_ref(v___y_1887_);
lean_del_object(v___x_1793_);
v_a_1884_ = v___x_1786_;
goto v___jp_1883_;
}
else
{
lean_object* v___x_1890_; 
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 1);
lean_ctor_set(v___x_1793_, 0, v___y_1887_);
v___x_1890_ = v___x_1793_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___y_1887_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
v___jp_1892_:
{
uint8_t v___x_1894_; 
v___x_1894_ = l_Lean_Exception_isInterrupt(v_a_1893_);
if (v___x_1894_ == 0)
{
uint8_t v___x_1895_; 
lean_inc_ref(v_a_1893_);
v___x_1895_ = l_Lean_Exception_isRuntime(v_a_1893_);
v___y_1887_ = v_a_1893_;
v___y_1888_ = v___x_1895_;
goto v___jp_1886_;
}
else
{
v___y_1887_ = v_a_1893_;
v___y_1888_ = v___x_1894_;
goto v___jp_1886_;
}
}
v___jp_1896_:
{
if (lean_obj_tag(v___y_1897_) == 0)
{
lean_object* v_a_1898_; 
lean_del_object(v___x_1793_);
v_a_1898_ = lean_ctor_get(v___y_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___y_1897_);
if (lean_obj_tag(v_a_1898_) == 0)
{
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
v_a_1751_ = v___x_1786_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_1899_; 
v_a_1899_ = lean_ctor_get(v_a_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v_a_1898_);
v_a_1884_ = v_a_1899_;
goto v___jp_1883_;
}
}
else
{
lean_object* v_a_1900_; 
v_a_1900_ = lean_ctor_get(v___y_1897_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___y_1897_);
v_a_1893_ = v_a_1900_;
goto v___jp_1892_;
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1922_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1790_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1790_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v___x_1930_; 
lean_inc(v___y_1748_);
lean_inc_ref(v___y_1747_);
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1745_);
lean_inc(v___x_1788_);
v___x_1930_ = lean_infer_type(v___x_1788_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1930_);
lean_inc(v_a_1931_);
lean_inc(v_a_1783_);
v___x_1932_ = l_Lean_Meta_isExprDefEq(v_a_1783_, v_a_1931_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; uint8_t v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = lean_unbox(v_a_1933_);
lean_dec(v_a_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_1787_, v___y_1747_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; uint8_t v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = lean_unbox(v_a_1936_);
lean_dec(v_a_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; 
lean_dec(v_a_1931_);
lean_inc(v___x_1788_);
v___x_1938_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_1783_, v___x_1788_, v___x_1775_, v___x_1778_, v___x_1786_, v___x_1786_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v___y_1756_ = v___x_1938_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1939_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3);
lean_inc(v_a_1743_);
v___x_1940_ = l_Nat_reprFast(v_a_1743_);
v___x_1941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
v___x_1942_ = l_Lean_MessageData_ofFormat(v___x_1941_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1939_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
lean_inc(v_a_1783_);
v___x_1946_ = l_Lean_MessageData_ofExpr(v_a_1783_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_MessageData_ofExpr(v_a_1931_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9);
v___x_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
lean_inc(v___x_1788_);
v___x_1954_ = l_Lean_MessageData_ofExpr(v___x_1788_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_1787_, v___x_1955_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
lean_inc(v___x_1788_);
v___x_1958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_1783_, v___x_1788_, v___x_1775_, v___x_1778_, v___x_1786_, v_a_1957_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v___y_1756_ = v___x_1958_;
goto v___jp_1755_;
}
else
{
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
return v___x_1956_;
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_a_1931_);
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1959_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1935_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1935_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v___x_1967_; 
lean_dec(v_a_1931_);
lean_dec(v_a_1783_);
lean_inc(v___x_1788_);
v___x_1967_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1778_, v___x_1788_, v___y_1746_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_dec_ref(v___x_1967_);
v_a_1751_ = v___x_1786_;
goto v___jp_1750_;
}
else
{
lean_dec(v_a_1743_);
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v_a_1931_);
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1968_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1932_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1932_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1976_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1930_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1930_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_a_1783_);
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1984_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1784_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1784_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_1992_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1782_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1782_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
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
lean_dec(v___x_1778_);
lean_dec(v_a_1743_);
v_a_2000_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1779_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1779_);
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
v___jp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v_a_1743_, v___x_1752_);
lean_dec(v_a_1743_);
v_a_1743_ = v___x_1753_;
v_b_1744_ = v_a_1751_;
goto _start;
}
v___jp_1755_:
{
if (lean_obj_tag(v___y_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1766_; 
v_a_1757_ = lean_ctor_get(v___y_1756_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___y_1756_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1759_ = v___y_1756_;
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___y_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
if (lean_obj_tag(v_a_1757_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; 
lean_dec(v_a_1743_);
v_a_1761_ = lean_ctor_get(v_a_1757_, 0);
lean_inc(v_a_1761_);
lean_dec_ref(v_a_1757_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v_a_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
else
{
lean_object* v_a_1765_; 
lean_del_object(v___x_1759_);
v_a_1765_ = lean_ctor_get(v_a_1757_, 0);
lean_inc(v_a_1765_);
lean_dec_ref(v_a_1757_);
v_a_1751_ = v_a_1765_;
goto v___jp_1750_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1743_);
v_a_1767_ = lean_ctor_get(v___y_1756_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___y_1756_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___y_1756_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___y_1756_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__4));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__6));
v___x_2013_ = l_Lean_stringToMessageData(v___x_2012_);
return v___x_2013_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__8));
v___x_2016_ = l_Lean_stringToMessageData(v___x_2015_);
return v___x_2016_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__10));
v___x_2019_ = l_Lean_stringToMessageData(v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10(lean_object* v_a_2020_, lean_object* v_expectedType_2021_, uint8_t v___x_2022_, uint8_t v_compile_2023_, uint8_t v_logCompileErrors_2024_, uint8_t v_isMeta_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; 
if (lean_obj_tag(v_x_2026_) == 5)
{
lean_object* v_fn_2073_; lean_object* v_arg_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_fn_2073_ = lean_ctor_get(v_x_2026_, 0);
lean_inc_ref(v_fn_2073_);
v_arg_2074_ = lean_ctor_get(v_x_2026_, 1);
lean_inc_ref(v_arg_2074_);
lean_dec_ref(v_x_2026_);
v___x_2075_ = lean_array_set(v_x_2027_, v_x_2028_, v_arg_2074_);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_nat_sub(v_x_2028_, v___x_2076_);
lean_dec(v_x_2028_);
v_x_2026_ = v_fn_2073_;
v_x_2027_ = v___x_2075_;
v_x_2028_ = v___x_2077_;
goto _start;
}
else
{
uint8_t v___x_2079_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v_cls_2151_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___x_2172_; 
lean_dec(v_x_2028_);
v___x_2079_ = 1;
v_cls_2151_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_2172_ = l_Lean_Expr_constName_x3f(v_x_2026_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_dec_ref(v_x_2027_);
lean_dec_ref(v_x_2026_);
v___y_2153_ = v___y_2029_;
v___y_2154_ = v___y_2030_;
v___y_2155_ = v___y_2031_;
v___y_2156_ = v___y_2032_;
goto v___jp_2152_;
}
else
{
lean_object* v_val_2173_; lean_object* v___x_2174_; 
v_val_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_val_2173_);
lean_dec_ref(v___x_2172_);
v___x_2174_ = l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(v_val_2173_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
if (lean_obj_tag(v_a_2175_) == 6)
{
lean_object* v_val_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v_a_2020_);
v_val_2176_ = lean_ctor_get(v_a_2175_, 0);
lean_inc_ref(v_val_2176_);
lean_dec_ref(v_a_2175_);
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2031_);
lean_inc(v___y_2030_);
lean_inc_ref(v___y_2029_);
lean_inc_ref(v_x_2026_);
v___x_2177_ = lean_infer_type(v_x_2026_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref(v___x_2177_);
v___x_2179_ = 0;
v___x_2180_ = l_Lean_Meta_forallMetaTelescope(v_a_2178_, v___x_2179_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v_snd_2182_; lean_object* v_fst_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2282_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
v_snd_2182_ = lean_ctor_get(v_a_2181_, 1);
v_fst_2183_ = lean_ctor_get(v_a_2181_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_a_2181_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2185_ = v_a_2181_;
v_isShared_2186_ = v_isSharedCheck_2282_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_snd_2182_);
lean_inc(v_fst_2183_);
lean_dec(v_a_2181_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2282_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_snd_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2280_; 
v_snd_2187_ = lean_ctor_get(v_snd_2182_, 1);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_snd_2182_);
if (v_isSharedCheck_2280_ == 0)
{
lean_object* v_unused_2281_; 
v_unused_2281_ = lean_ctor_get(v_snd_2182_, 0);
lean_dec(v_unused_2281_);
v___x_2189_ = v_snd_2182_;
v_isShared_2190_ = v_isSharedCheck_2280_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snd_2187_);
lean_dec(v_snd_2182_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2280_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2191_ = lean_array_get_size(v_x_2027_);
v___x_2228_ = lean_array_get_size(v_fst_2183_);
v___x_2229_ = lean_nat_dec_eq(v___x_2191_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec(v_snd_2187_);
lean_dec(v_fst_2183_);
lean_dec_ref(v_val_2176_);
lean_dec_ref(v_expectedType_2021_);
v___x_2230_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5);
v___x_2231_ = l_Lean_MessageData_ofExpr(v_x_2026_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 7);
lean_ctor_set(v___x_2189_, 1, v___x_2231_);
lean_ctor_set(v___x_2189_, 0, v___x_2230_);
v___x_2233_ = v___x_2189_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7);
if (v_isShared_2186_ == 0)
{
lean_ctor_set_tag(v___x_2185_, 7);
lean_ctor_set(v___x_2185_, 1, v___x_2234_);
lean_ctor_set(v___x_2185_, 0, v___x_2233_);
v___x_2236_ = v___x_2185_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2237_ = lean_array_to_list(v_x_2027_);
v___x_2238_ = lean_box(0);
v___x_2239_ = l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(v___x_2237_, v___x_2238_);
v___x_2240_ = l_Lean_MessageData_ofList(v___x_2239_);
v___x_2241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2236_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_2241_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2242_;
}
}
}
else
{
lean_object* v___x_2245_; 
lean_inc_ref(v_expectedType_2021_);
v___x_2245_ = l_Lean_Meta_isExprDefEq(v_expectedType_2021_, v_snd_2187_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; uint8_t v___x_2247_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = lean_unbox(v_a_2246_);
lean_dec(v_a_2246_);
if (v___x_2247_ == 0)
{
lean_object* v_toConstantVal_2248_; lean_object* v_name_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_dec(v_fst_2183_);
lean_dec_ref(v_x_2027_);
lean_dec_ref(v_x_2026_);
v_toConstantVal_2248_ = lean_ctor_get(v_val_2176_, 0);
lean_inc_ref(v_toConstantVal_2248_);
lean_dec_ref(v_val_2176_);
v_name_2249_ = lean_ctor_get(v_toConstantVal_2248_, 0);
lean_inc(v_name_2249_);
lean_dec_ref(v_toConstantVal_2248_);
v___x_2250_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9);
v___x_2251_ = l_Lean_MessageData_ofExpr(v_expectedType_2021_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 7);
lean_ctor_set(v___x_2189_, 1, v___x_2251_);
lean_ctor_set(v___x_2189_, 0, v___x_2250_);
v___x_2253_ = v___x_2189_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11);
if (v_isShared_2186_ == 0)
{
lean_ctor_set_tag(v___x_2185_, 7);
lean_ctor_set(v___x_2185_, 1, v___x_2254_);
lean_ctor_set(v___x_2185_, 0, v___x_2253_);
v___x_2256_ = v___x_2185_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v___x_2257_ = l_Lean_MessageData_ofConstName(v_name_2249_, v___x_2022_);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_2260_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
else
{
lean_del_object(v___x_2189_);
lean_del_object(v___x_2185_);
lean_dec_ref(v_expectedType_2021_);
v___y_2193_ = v___y_2029_;
v___y_2194_ = v___y_2030_;
v___y_2195_ = v___y_2031_;
v___y_2196_ = v___y_2032_;
goto v___jp_2192_;
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_del_object(v___x_2189_);
lean_del_object(v___x_2185_);
lean_dec(v_fst_2183_);
lean_dec_ref(v_val_2176_);
lean_dec_ref(v_x_2027_);
lean_dec_ref(v_x_2026_);
lean_dec_ref(v_expectedType_2021_);
v_a_2272_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2245_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2245_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
v___jp_2192_:
{
lean_object* v_numParams_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_numParams_2197_ = lean_ctor_get(v_val_2176_, 3);
lean_inc(v_numParams_2197_);
lean_dec_ref(v_val_2176_);
v___x_2198_ = lean_box(0);
v___x_2199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(v___x_2191_, v_fst_2183_, v_x_2027_, v_compile_2023_, v_logCompileErrors_2024_, v_isMeta_2025_, v___x_2022_, v_numParams_2197_, v___x_2198_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec_ref(v_x_2027_);
if (lean_obj_tag(v___x_2199_) == 0)
{
size_t v_sz_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v___x_2199_);
v_sz_2200_ = lean_array_size(v_fst_2183_);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_2200_, v___x_2201_, v_fst_2183_, v___y_2194_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2211_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = l_Lean_mkAppN(v_x_2026_, v_a_2203_);
lean_dec(v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2207_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec_ref(v_x_2026_);
v_a_2212_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2202_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2202_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_fst_2183_);
lean_dec_ref(v_x_2026_);
v_a_2220_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2199_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2199_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_val_2176_);
lean_dec_ref(v_x_2027_);
lean_dec_ref(v_x_2026_);
lean_dec_ref(v_expectedType_2021_);
v_a_2283_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2180_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2180_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_dec_ref(v_val_2176_);
lean_dec_ref(v_x_2027_);
lean_dec_ref(v_x_2026_);
lean_dec_ref(v_expectedType_2021_);
return v___x_2177_;
}
}
else
{
lean_dec(v_a_2175_);
lean_dec_ref(v_x_2027_);
lean_dec_ref(v_x_2026_);
v___y_2153_ = v___y_2029_;
v___y_2154_ = v___y_2030_;
v___y_2155_ = v___y_2031_;
v___y_2156_ = v___y_2032_;
goto v___jp_2152_;
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_x_2027_);
lean_dec_ref(v_x_2026_);
lean_dec_ref(v_expectedType_2021_);
lean_dec_ref(v_a_2020_);
v_a_2291_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2174_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2174_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
v___jp_2080_:
{
lean_object* v_options_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_options_2085_ = lean_ctor_get(v___y_2083_, 2);
v___x_2086_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2087_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2085_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref(v_expectedType_2021_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_a_2020_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; 
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc_ref(v_a_2020_);
v___x_2089_ = lean_infer_type(v_a_2020_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2089_);
lean_inc_ref(v_expectedType_2021_);
v___x_2091_ = l_Lean_Meta_isExprDefEq(v_expectedType_2021_, v_a_2090_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2142_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2142_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2142_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_unbox(v_a_2092_);
lean_dec(v_a_2092_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v_a_2099_; lean_object* v___x_2100_; 
lean_del_object(v___x_2094_);
v___x_2097_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1));
v___x_2098_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2097_, v___y_2084_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2098_);
lean_inc(v_a_2099_);
v___x_2100_ = l_Lean_Meta_mkAuxDefinition(v_a_2099_, v_expectedType_2021_, v_a_2020_, v___x_2022_, v___x_2022_, v___x_2079_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = 3;
lean_inc(v_a_2099_);
v___x_2103_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(v_a_2099_, v___x_2102_, v___y_2082_, v___y_2084_);
lean_dec_ref(v___x_2103_);
if (v_isMeta_2025_ == 0)
{
v___y_2057_ = v_a_2099_;
v___y_2058_ = v_a_2101_;
v___y_2059_ = v___y_2083_;
v___y_2060_ = v___y_2084_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2104_; lean_object* v_env_2105_; lean_object* v_nextMacroScope_2106_; lean_object* v_ngen_2107_; lean_object* v_auxDeclNGen_2108_; lean_object* v_traceState_2109_; lean_object* v_messages_2110_; lean_object* v_infoState_2111_; lean_object* v_snapshotTasks_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2137_; 
v___x_2104_ = lean_st_ref_take(v___y_2084_);
v_env_2105_ = lean_ctor_get(v___x_2104_, 0);
v_nextMacroScope_2106_ = lean_ctor_get(v___x_2104_, 1);
v_ngen_2107_ = lean_ctor_get(v___x_2104_, 2);
v_auxDeclNGen_2108_ = lean_ctor_get(v___x_2104_, 3);
v_traceState_2109_ = lean_ctor_get(v___x_2104_, 4);
v_messages_2110_ = lean_ctor_get(v___x_2104_, 6);
v_infoState_2111_ = lean_ctor_get(v___x_2104_, 7);
v_snapshotTasks_2112_ = lean_ctor_get(v___x_2104_, 8);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v___x_2104_, 5);
lean_dec(v_unused_2138_);
v___x_2114_ = v___x_2104_;
v_isShared_2115_ = v_isSharedCheck_2137_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_snapshotTasks_2112_);
lean_inc(v_infoState_2111_);
lean_inc(v_messages_2110_);
lean_inc(v_traceState_2109_);
lean_inc(v_auxDeclNGen_2108_);
lean_inc(v_ngen_2107_);
lean_inc(v_nextMacroScope_2106_);
lean_inc(v_env_2105_);
lean_dec(v___x_2104_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2137_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_inc(v_a_2099_);
v___x_2116_ = l_Lean_markMeta(v_env_2105_, v_a_2099_);
v___x_2117_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 5, v___x_2117_);
lean_ctor_set(v___x_2114_, 0, v___x_2116_);
v___x_2119_ = v___x_2114_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_nextMacroScope_2106_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_ngen_2107_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_auxDeclNGen_2108_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_traceState_2109_);
lean_ctor_set(v_reuseFailAlloc_2136_, 5, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2136_, 6, v_messages_2110_);
lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_infoState_2111_);
lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_snapshotTasks_2112_);
v___x_2119_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v_mctx_2122_; lean_object* v_zetaDeltaFVarIds_2123_; lean_object* v_postponed_2124_; lean_object* v_diag_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2134_; 
v___x_2120_ = lean_st_ref_set(v___y_2084_, v___x_2119_);
v___x_2121_ = lean_st_ref_take(v___y_2082_);
v_mctx_2122_ = lean_ctor_get(v___x_2121_, 0);
v_zetaDeltaFVarIds_2123_ = lean_ctor_get(v___x_2121_, 2);
v_postponed_2124_ = lean_ctor_get(v___x_2121_, 3);
v_diag_2125_ = lean_ctor_get(v___x_2121_, 4);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v___x_2121_, 1);
lean_dec(v_unused_2135_);
v___x_2127_ = v___x_2121_;
v_isShared_2128_ = v_isSharedCheck_2134_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_diag_2125_);
lean_inc(v_postponed_2124_);
lean_inc(v_zetaDeltaFVarIds_2123_);
lean_inc(v_mctx_2122_);
lean_dec(v___x_2121_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2134_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v___x_2129_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_mctx_2122_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_zetaDeltaFVarIds_2123_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_postponed_2124_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v_diag_2125_);
v___x_2131_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_st_ref_set(v___y_2082_, v___x_2131_);
v___y_2057_ = v_a_2099_;
v___y_2058_ = v_a_2101_;
v___y_2059_ = v___y_2083_;
v___y_2060_ = v___y_2084_;
goto v___jp_2056_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2099_);
return v___x_2100_;
}
}
else
{
lean_object* v___x_2140_; 
lean_dec_ref(v_expectedType_2021_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v_a_2020_);
v___x_2140_ = v___x_2094_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2020_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec_ref(v_expectedType_2021_);
lean_dec_ref(v_a_2020_);
v_a_2143_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2091_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2091_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2021_);
lean_dec_ref(v_a_2020_);
return v___x_2089_;
}
}
}
v___jp_2152_:
{
lean_object* v___x_2157_; lean_object* v_a_2158_; uint8_t v___x_2159_; 
v___x_2157_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2151_, v___y_2155_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = lean_unbox(v_a_2158_);
lean_dec(v_a_2158_);
if (v___x_2159_ == 0)
{
v___y_2081_ = v___y_2153_;
v___y_2082_ = v___y_2154_;
v___y_2083_ = v___y_2155_;
v___y_2084_ = v___y_2156_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2160_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3);
lean_inc_ref(v_a_2020_);
v___x_2161_ = l_Lean_MessageData_ofExpr(v_a_2020_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2151_, v___x_2162_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec_ref(v___x_2163_);
v___y_2081_ = v___y_2153_;
v___y_2082_ = v___y_2154_;
v___y_2083_ = v___y_2155_;
v___y_2084_ = v___y_2156_;
goto v___jp_2080_;
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_expectedType_2021_);
lean_dec_ref(v_a_2020_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
}
v___jp_2034_:
{
lean_object* v___x_2039_; 
lean_inc_ref(v___y_2037_);
v___x_2039_ = l_Lean_enableRealizationsForConst(v___y_2035_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2047_);
v___x_2041_ = v___x_2039_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v___x_2039_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___y_2036_);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___y_2036_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v___y_2036_);
v_a_2048_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2039_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2039_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
v___jp_2056_:
{
if (v_compile_2023_ == 0)
{
v___y_2035_ = v___y_2057_;
v___y_2036_ = v___y_2058_;
v___y_2037_ = v___y_2059_;
v___y_2038_ = v___y_2060_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = lean_unsigned_to_nat(1u);
v___x_2062_ = lean_mk_empty_array_with_capacity(v___x_2061_);
lean_inc(v___y_2057_);
v___x_2063_ = lean_array_push(v___x_2062_, v___y_2057_);
v___x_2064_ = l_Lean_compileDecls(v___x_2063_, v_logCompileErrors_2024_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_dec_ref(v___x_2064_);
v___y_2035_ = v___y_2057_;
v___y_2036_ = v___y_2058_;
v___y_2037_ = v___y_2059_;
v___y_2038_ = v___y_2060_;
goto v___jp_2034_;
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
}
static uint64_t _init_l_Lean_Meta_normalizeInstance___closed__0(void){
_start:
{
uint8_t v___x_2299_; uint64_t v___x_2300_; 
v___x_2299_ = 3;
v___x_2300_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_Meta_normalizeInstance___closed__2(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_Meta_normalizeInstance___closed__1));
v___x_2303_ = l_Lean_stringToMessageData(v___x_2302_);
return v___x_2303_;
}
}
static double _init_l_Lean_Meta_normalizeInstance___closed__3(void){
_start:
{
lean_object* v___x_2304_; double v___x_2305_; 
v___x_2304_ = lean_unsigned_to_nat(1000000000u);
v___x_2305_ = lean_float_of_nat(v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(lean_object* v_upperBound_2306_, lean_object* v_fst_2307_, lean_object* v_args_2308_, uint8_t v___x_2309_, uint8_t v_compile_2310_, uint8_t v_logCompileErrors_2311_, uint8_t v_isMeta_2312_, uint8_t v___x_2313_, lean_object* v_a_2314_, lean_object* v_b_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_a_2322_; lean_object* v___y_2327_; uint8_t v___x_2346_; 
v___x_2346_ = lean_nat_dec_lt(v_a_2314_, v_upperBound_2306_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; 
lean_dec(v_a_2314_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v_b_2315_);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = lean_array_fget_borrowed(v_fst_2307_, v_a_2314_);
v___x_2349_ = l_Lean_Expr_mvarId_x21(v___x_2348_);
lean_inc(v___x_2349_);
v___x_2350_ = l_Lean_MVarId_getDecl(v___x_2349_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v_type_2352_; lean_object* v___x_2353_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
v_type_2352_ = lean_ctor_get(v_a_2351_, 2);
lean_inc_ref(v_type_2352_);
lean_dec(v_a_2351_);
v___x_2353_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2352_, v___y_2317_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v___x_2353_);
lean_inc(v_a_2354_);
v___x_2355_ = l_Lean_Meta_isProp(v_a_2354_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2357_; lean_object* v_cls_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = lean_box(0);
v_cls_2358_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_2359_ = lean_array_fget_borrowed(v_args_2308_, v_a_2314_);
v___x_2360_ = lean_unbox(v_a_2356_);
lean_dec(v_a_2356_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
lean_inc(v_a_2354_);
v___x_2361_ = l_Lean_Meta_isClass_x3f(v_a_2354_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2493_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2493_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2493_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_a_2367_; lean_object* v___y_2370_; uint8_t v___y_2371_; lean_object* v_a_2376_; lean_object* v___y_2380_; 
if (lean_obj_tag(v_a_2362_) == 0)
{
if (v___x_2313_ == 0)
{
lean_object* v_options_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
lean_del_object(v___x_2364_);
v_options_2406_ = lean_ctor_get(v___y_2318_, 2);
v___x_2407_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2408_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2406_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_dec(v_a_2354_);
lean_inc(v___x_2359_);
v___x_2409_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2349_, v___x_2359_, v___y_2317_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_dec_ref(v___x_2409_);
v_a_2322_ = v___x_2357_;
goto v___jp_2321_;
}
else
{
lean_dec(v_a_2314_);
return v___x_2409_;
}
}
else
{
lean_object* v___x_2410_; 
lean_inc(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc(v___x_2359_);
v___x_2410_ = lean_infer_type(v___x_2359_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref(v___x_2410_);
lean_inc(v_a_2354_);
v___x_2412_ = l_Lean_Meta_isExprDefEq(v_a_2354_, v_a_2411_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; uint8_t v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v___x_2414_ = lean_unbox(v_a_2413_);
lean_dec(v_a_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1));
v___x_2416_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2415_, v___y_2319_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2416_);
lean_inc(v___x_2359_);
lean_inc(v_a_2417_);
v___x_2418_ = l_Lean_Meta_mkAuxDefinition(v_a_2417_, v_a_2354_, v___x_2359_, v___x_2313_, v___x_2313_, v___x_2309_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2349_, v_a_2419_, v___y_2317_);
if (lean_obj_tag(v___x_2420_) == 0)
{
uint8_t v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref(v___x_2420_);
v___x_2421_ = 0;
lean_inc(v_a_2417_);
v___x_2422_ = l_Lean_Meta_setInlineAttribute(v_a_2417_, v___x_2421_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_dec_ref(v___x_2422_);
if (v_isMeta_2312_ == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_2417_, v___x_2357_, v_compile_2310_, v_logCompileErrors_2311_, v___x_2357_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2327_ = v___x_2423_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2424_; lean_object* v_env_2425_; lean_object* v_nextMacroScope_2426_; lean_object* v_ngen_2427_; lean_object* v_auxDeclNGen_2428_; lean_object* v_traceState_2429_; lean_object* v_messages_2430_; lean_object* v_infoState_2431_; lean_object* v_snapshotTasks_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2458_; 
v___x_2424_ = lean_st_ref_take(v___y_2319_);
v_env_2425_ = lean_ctor_get(v___x_2424_, 0);
v_nextMacroScope_2426_ = lean_ctor_get(v___x_2424_, 1);
v_ngen_2427_ = lean_ctor_get(v___x_2424_, 2);
v_auxDeclNGen_2428_ = lean_ctor_get(v___x_2424_, 3);
v_traceState_2429_ = lean_ctor_get(v___x_2424_, 4);
v_messages_2430_ = lean_ctor_get(v___x_2424_, 6);
v_infoState_2431_ = lean_ctor_get(v___x_2424_, 7);
v_snapshotTasks_2432_ = lean_ctor_get(v___x_2424_, 8);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v___x_2424_, 5);
lean_dec(v_unused_2459_);
v___x_2434_ = v___x_2424_;
v_isShared_2435_ = v_isSharedCheck_2458_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_snapshotTasks_2432_);
lean_inc(v_infoState_2431_);
lean_inc(v_messages_2430_);
lean_inc(v_traceState_2429_);
lean_inc(v_auxDeclNGen_2428_);
lean_inc(v_ngen_2427_);
lean_inc(v_nextMacroScope_2426_);
lean_inc(v_env_2425_);
lean_dec(v___x_2424_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2458_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
lean_inc(v_a_2417_);
v___x_2436_ = l_Lean_markMeta(v_env_2425_, v_a_2417_);
v___x_2437_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 5, v___x_2437_);
lean_ctor_set(v___x_2434_, 0, v___x_2436_);
v___x_2439_ = v___x_2434_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_nextMacroScope_2426_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_ngen_2427_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_auxDeclNGen_2428_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_traceState_2429_);
lean_ctor_set(v_reuseFailAlloc_2457_, 5, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2457_, 6, v_messages_2430_);
lean_ctor_set(v_reuseFailAlloc_2457_, 7, v_infoState_2431_);
lean_ctor_set(v_reuseFailAlloc_2457_, 8, v_snapshotTasks_2432_);
v___x_2439_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v_mctx_2442_; lean_object* v_zetaDeltaFVarIds_2443_; lean_object* v_postponed_2444_; lean_object* v_diag_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2455_; 
v___x_2440_ = lean_st_ref_set(v___y_2319_, v___x_2439_);
v___x_2441_ = lean_st_ref_take(v___y_2317_);
v_mctx_2442_ = lean_ctor_get(v___x_2441_, 0);
v_zetaDeltaFVarIds_2443_ = lean_ctor_get(v___x_2441_, 2);
v_postponed_2444_ = lean_ctor_get(v___x_2441_, 3);
v_diag_2445_ = lean_ctor_get(v___x_2441_, 4);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; 
v_unused_2456_ = lean_ctor_get(v___x_2441_, 1);
lean_dec(v_unused_2456_);
v___x_2447_ = v___x_2441_;
v_isShared_2448_ = v_isSharedCheck_2455_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_diag_2445_);
lean_inc(v_postponed_2444_);
lean_inc(v_zetaDeltaFVarIds_2443_);
lean_inc(v_mctx_2442_);
lean_dec(v___x_2441_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2455_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v___x_2449_);
v___x_2451_ = v___x_2447_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_mctx_2442_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v_zetaDeltaFVarIds_2443_);
lean_ctor_set(v_reuseFailAlloc_2454_, 3, v_postponed_2444_);
lean_ctor_set(v_reuseFailAlloc_2454_, 4, v_diag_2445_);
v___x_2451_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_st_ref_set(v___y_2317_, v___x_2451_);
v___x_2453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_2417_, v___x_2357_, v_compile_2310_, v_logCompileErrors_2311_, v___x_2357_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2327_ = v___x_2453_;
goto v___jp_2326_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2417_);
lean_dec(v_a_2314_);
return v___x_2422_;
}
}
else
{
lean_dec(v_a_2417_);
lean_dec(v_a_2314_);
return v___x_2420_;
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_a_2417_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2460_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2418_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2418_);
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
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2468_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2416_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2416_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v___x_2476_; 
lean_dec(v_a_2354_);
lean_inc(v___x_2359_);
v___x_2476_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2349_, v___x_2359_, v___y_2317_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_dec_ref(v___x_2476_);
v_a_2322_ = v___x_2357_;
goto v___jp_2321_;
}
else
{
lean_dec(v_a_2314_);
return v___x_2476_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2477_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2412_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2412_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2485_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2410_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2410_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
else
{
goto v___jp_2384_;
}
}
else
{
lean_dec_ref(v_a_2362_);
goto v___jp_2384_;
}
v___jp_2366_:
{
lean_object* v___x_2368_; 
lean_inc(v___x_2359_);
v___x_2368_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_2359_, v_a_2354_, v_compile_2310_, v_logCompileErrors_2311_, v_isMeta_2312_, v___x_2349_, v___x_2357_, v_a_2367_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2327_ = v___x_2368_;
goto v___jp_2326_;
}
v___jp_2369_:
{
if (v___y_2371_ == 0)
{
lean_dec_ref(v___y_2370_);
lean_del_object(v___x_2364_);
v_a_2367_ = v___x_2357_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2373_; 
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set_tag(v___x_2364_, 1);
lean_ctor_set(v___x_2364_, 0, v___y_2370_);
v___x_2373_ = v___x_2364_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___y_2370_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
v___jp_2375_:
{
uint8_t v___x_2377_; 
v___x_2377_ = l_Lean_Exception_isInterrupt(v_a_2376_);
if (v___x_2377_ == 0)
{
uint8_t v___x_2378_; 
lean_inc_ref(v_a_2376_);
v___x_2378_ = l_Lean_Exception_isRuntime(v_a_2376_);
v___y_2370_ = v_a_2376_;
v___y_2371_ = v___x_2378_;
goto v___jp_2369_;
}
else
{
v___y_2370_ = v_a_2376_;
v___y_2371_ = v___x_2377_;
goto v___jp_2369_;
}
}
v___jp_2379_:
{
if (lean_obj_tag(v___y_2380_) == 0)
{
lean_object* v_a_2381_; 
lean_del_object(v___x_2364_);
v_a_2381_ = lean_ctor_get(v___y_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref(v___y_2380_);
if (lean_obj_tag(v_a_2381_) == 0)
{
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
v_a_2322_ = v___x_2357_;
goto v___jp_2321_;
}
else
{
lean_object* v_a_2382_; 
v_a_2382_ = lean_ctor_get(v_a_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref(v_a_2381_);
v_a_2367_ = v_a_2382_;
goto v___jp_2366_;
}
}
else
{
lean_object* v_a_2383_; 
v_a_2383_ = lean_ctor_get(v___y_2380_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___y_2380_);
v_a_2376_ = v_a_2383_;
goto v___jp_2375_;
}
}
v___jp_2384_:
{
lean_object* v_options_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v_options_2385_ = lean_ctor_get(v___y_2318_, 2);
v___x_2386_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2387_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; 
lean_del_object(v___x_2364_);
lean_inc(v___x_2359_);
v___x_2388_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_2359_, v_a_2354_, v_compile_2310_, v_logCompileErrors_2311_, v_isMeta_2312_, v___x_2349_, v___x_2357_, v___x_2357_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2327_ = v___x_2388_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_box(0);
lean_inc(v_a_2354_);
v___x_2390_ = l_Lean_Meta_trySynthInstance(v_a_2354_, v___x_2389_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2390_);
if (lean_obj_tag(v_a_2391_) == 1)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2392_ = lean_ctor_get(v_a_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v_a_2391_);
v___x_2393_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2358_, v___y_2318_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; uint8_t v___x_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = lean_unbox(v_a_2394_);
lean_dec(v_a_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
lean_inc(v___x_2349_);
v___x_2396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_2349_, v_a_2392_, v___x_2357_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2380_ = v___x_2396_;
goto v___jp_2379_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2397_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1);
lean_inc(v_a_2392_);
v___x_2398_ = l_Lean_MessageData_ofExpr(v_a_2392_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2358_, v___x_2399_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref(v___x_2400_);
lean_inc(v___x_2349_);
v___x_2402_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_2349_, v_a_2392_, v_a_2401_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2380_ = v___x_2402_;
goto v___jp_2379_;
}
else
{
lean_object* v_a_2403_; 
lean_dec(v_a_2392_);
v_a_2403_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2400_);
v_a_2376_ = v_a_2403_;
goto v___jp_2375_;
}
}
}
else
{
lean_object* v_a_2404_; 
lean_dec(v_a_2392_);
v_a_2404_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2404_);
lean_dec_ref(v___x_2393_);
v_a_2376_ = v_a_2404_;
goto v___jp_2375_;
}
}
else
{
lean_dec(v_a_2391_);
lean_del_object(v___x_2364_);
v_a_2367_ = v___x_2357_;
goto v___jp_2366_;
}
}
else
{
lean_object* v_a_2405_; 
v_a_2405_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2390_);
v_a_2376_ = v_a_2405_;
goto v___jp_2375_;
}
}
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2494_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2361_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2361_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_object* v___x_2502_; 
lean_inc(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc(v___x_2359_);
v___x_2502_ = lean_infer_type(v___x_2359_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v___x_2502_);
lean_inc(v_a_2503_);
lean_inc(v_a_2354_);
v___x_2504_ = l_Lean_Meta_isExprDefEq(v_a_2354_, v_a_2503_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; uint8_t v___x_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref(v___x_2504_);
v___x_2506_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2358_, v___y_2318_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; uint8_t v___x_2509_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref(v___x_2507_);
v___x_2509_ = lean_unbox(v_a_2508_);
lean_dec(v_a_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
lean_dec(v_a_2503_);
lean_inc(v___x_2359_);
v___x_2510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_2354_, v___x_2359_, v___x_2309_, v___x_2349_, v___x_2357_, v___x_2357_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2327_ = v___x_2510_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2511_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3);
lean_inc(v_a_2314_);
v___x_2512_ = l_Nat_reprFast(v_a_2314_);
v___x_2513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
v___x_2514_ = l_Lean_MessageData_ofFormat(v___x_2513_);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2511_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
lean_inc(v_a_2354_);
v___x_2518_ = l_Lean_MessageData_ofExpr(v_a_2354_);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_Lean_MessageData_ofExpr(v_a_2503_);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
lean_inc(v___x_2359_);
v___x_2526_ = l_Lean_MessageData_ofExpr(v___x_2359_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2358_, v___x_2527_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v___x_2528_);
lean_inc(v___x_2359_);
v___x_2530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_2354_, v___x_2359_, v___x_2309_, v___x_2349_, v___x_2357_, v_a_2529_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2327_ = v___x_2530_;
goto v___jp_2326_;
}
else
{
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
return v___x_2528_;
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_a_2503_);
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2531_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2507_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2507_);
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
else
{
lean_object* v___x_2539_; 
lean_dec(v_a_2503_);
lean_dec(v_a_2354_);
lean_inc(v___x_2359_);
v___x_2539_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2349_, v___x_2359_, v___y_2317_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_dec_ref(v___x_2539_);
v_a_2322_ = v___x_2357_;
goto v___jp_2321_;
}
else
{
lean_dec(v_a_2314_);
return v___x_2539_;
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_a_2503_);
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2540_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2504_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2504_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2548_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2502_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2502_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
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
return v___x_2553_;
}
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_a_2354_);
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2556_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2355_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2355_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2564_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2353_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2353_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v___x_2349_);
lean_dec(v_a_2314_);
v_a_2572_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2350_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2350_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
v___jp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_unsigned_to_nat(1u);
v___x_2324_ = lean_nat_add(v_a_2314_, v___x_2323_);
lean_dec(v_a_2314_);
v_a_2314_ = v___x_2324_;
v_b_2315_ = v_a_2322_;
goto _start;
}
v___jp_2326_:
{
if (lean_obj_tag(v___y_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2337_; 
v_a_2328_ = lean_ctor_get(v___y_2327_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___y_2327_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2330_ = v___y_2327_;
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___y_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
if (lean_obj_tag(v_a_2328_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; 
lean_dec(v_a_2314_);
v_a_2332_ = lean_ctor_get(v_a_2328_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v_a_2328_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v_a_2332_);
v___x_2334_ = v___x_2330_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
else
{
lean_object* v_a_2336_; 
lean_del_object(v___x_2330_);
v_a_2336_ = lean_ctor_get(v_a_2328_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v_a_2328_);
v_a_2322_ = v_a_2336_;
goto v___jp_2321_;
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2314_);
v_a_2338_ = lean_ctor_get(v___y_2327_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___y_2327_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___y_2327_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___y_2327_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(lean_object* v_a_2580_, lean_object* v_expectedType_2581_, uint8_t v___x_2582_, uint8_t v___x_2583_, uint8_t v_compile_2584_, uint8_t v_logCompileErrors_2585_, uint8_t v_isMeta_2586_, lean_object* v_x_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; 
if (lean_obj_tag(v_x_2587_) == 5)
{
lean_object* v_fn_2705_; lean_object* v_arg_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_fn_2705_ = lean_ctor_get(v_x_2587_, 0);
lean_inc_ref(v_fn_2705_);
v_arg_2706_ = lean_ctor_get(v_x_2587_, 1);
lean_inc_ref(v_arg_2706_);
lean_dec_ref(v_x_2587_);
v___x_2707_ = lean_array_set(v_x_2588_, v_x_2589_, v_arg_2706_);
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_nat_sub(v_x_2589_, v___x_2708_);
lean_dec(v_x_2589_);
v_x_2587_ = v_fn_2705_;
v_x_2588_ = v___x_2707_;
v_x_2589_ = v___x_2709_;
goto _start;
}
else
{
lean_object* v_cls_2711_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___x_2732_; 
lean_dec(v_x_2589_);
v_cls_2711_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_2732_ = l_Lean_Expr_constName_x3f(v_x_2587_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_dec_ref(v_x_2588_);
lean_dec_ref(v_x_2587_);
v___y_2713_ = v___y_2590_;
v___y_2714_ = v___y_2591_;
v___y_2715_ = v___y_2592_;
v___y_2716_ = v___y_2593_;
goto v___jp_2712_;
}
else
{
lean_object* v_val_2733_; lean_object* v___x_2734_; 
v_val_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_val_2733_);
lean_dec_ref(v___x_2732_);
v___x_2734_ = l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(v_val_2733_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref(v___x_2734_);
if (lean_obj_tag(v_a_2735_) == 6)
{
lean_object* v_val_2736_; lean_object* v___x_2737_; 
lean_dec_ref(v_a_2580_);
v_val_2736_ = lean_ctor_get(v_a_2735_, 0);
lean_inc_ref(v_val_2736_);
lean_dec_ref(v_a_2735_);
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc_ref(v_x_2587_);
v___x_2737_ = lean_infer_type(v_x_2587_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref(v___x_2737_);
v___x_2739_ = 0;
v___x_2740_ = l_Lean_Meta_forallMetaTelescope(v_a_2738_, v___x_2739_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v_snd_2742_; lean_object* v_fst_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2842_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2740_);
v_snd_2742_ = lean_ctor_get(v_a_2741_, 1);
v_fst_2743_ = lean_ctor_get(v_a_2741_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_a_2741_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2745_ = v_a_2741_;
v_isShared_2746_ = v_isSharedCheck_2842_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_snd_2742_);
lean_inc(v_fst_2743_);
lean_dec(v_a_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2842_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_snd_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2840_; 
v_snd_2747_ = lean_ctor_get(v_snd_2742_, 1);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_snd_2742_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v_snd_2742_, 0);
lean_dec(v_unused_2841_);
v___x_2749_ = v_snd_2742_;
v_isShared_2750_ = v_isSharedCheck_2840_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_snd_2747_);
lean_dec(v_snd_2742_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2840_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2751_ = lean_array_get_size(v_x_2588_);
v___x_2788_ = lean_array_get_size(v_fst_2743_);
v___x_2789_ = lean_nat_dec_eq(v___x_2751_, v___x_2788_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
lean_dec(v_snd_2747_);
lean_dec(v_fst_2743_);
lean_dec_ref(v_val_2736_);
lean_dec_ref(v_expectedType_2581_);
v___x_2790_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5);
v___x_2791_ = l_Lean_MessageData_ofExpr(v_x_2587_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 7);
lean_ctor_set(v___x_2749_, 1, v___x_2791_);
lean_ctor_set(v___x_2749_, 0, v___x_2790_);
v___x_2793_ = v___x_2749_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2794_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7);
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 7);
lean_ctor_set(v___x_2745_, 1, v___x_2794_);
lean_ctor_set(v___x_2745_, 0, v___x_2793_);
v___x_2796_ = v___x_2745_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2797_ = lean_array_to_list(v_x_2588_);
v___x_2798_ = lean_box(0);
v___x_2799_ = l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(v___x_2797_, v___x_2798_);
v___x_2800_ = l_Lean_MessageData_ofList(v___x_2799_);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2796_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_2801_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
return v___x_2802_;
}
}
}
else
{
lean_object* v___x_2805_; 
lean_inc_ref(v_expectedType_2581_);
v___x_2805_ = l_Lean_Meta_isExprDefEq(v_expectedType_2581_, v_snd_2747_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; uint8_t v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = lean_unbox(v_a_2806_);
lean_dec(v_a_2806_);
if (v___x_2807_ == 0)
{
lean_object* v_toConstantVal_2808_; lean_object* v_name_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
lean_dec(v_fst_2743_);
lean_dec_ref(v_x_2588_);
lean_dec_ref(v_x_2587_);
v_toConstantVal_2808_ = lean_ctor_get(v_val_2736_, 0);
lean_inc_ref(v_toConstantVal_2808_);
lean_dec_ref(v_val_2736_);
v_name_2809_ = lean_ctor_get(v_toConstantVal_2808_, 0);
lean_inc(v_name_2809_);
lean_dec_ref(v_toConstantVal_2808_);
v___x_2810_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9);
v___x_2811_ = l_Lean_MessageData_ofExpr(v_expectedType_2581_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 7);
lean_ctor_set(v___x_2749_, 1, v___x_2811_);
lean_ctor_set(v___x_2749_, 0, v___x_2810_);
v___x_2813_ = v___x_2749_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2814_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11);
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 7);
lean_ctor_set(v___x_2745_, 1, v___x_2814_);
lean_ctor_set(v___x_2745_, 0, v___x_2813_);
v___x_2816_ = v___x_2745_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
v___x_2817_ = l_Lean_MessageData_ofConstName(v_name_2809_, v___x_2582_);
v___x_2818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2816_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3);
v___x_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2818_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_2820_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
else
{
lean_del_object(v___x_2749_);
lean_del_object(v___x_2745_);
lean_dec_ref(v_expectedType_2581_);
v___y_2753_ = v___y_2590_;
v___y_2754_ = v___y_2591_;
v___y_2755_ = v___y_2592_;
v___y_2756_ = v___y_2593_;
goto v___jp_2752_;
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_del_object(v___x_2749_);
lean_del_object(v___x_2745_);
lean_dec(v_fst_2743_);
lean_dec_ref(v_val_2736_);
lean_dec_ref(v_x_2588_);
lean_dec_ref(v_x_2587_);
lean_dec_ref(v_expectedType_2581_);
v_a_2832_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2805_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2805_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
v___jp_2752_:
{
lean_object* v_numParams_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_numParams_2757_ = lean_ctor_get(v_val_2736_, 3);
lean_inc(v_numParams_2757_);
lean_dec_ref(v_val_2736_);
v___x_2758_ = lean_box(0);
v___x_2759_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(v___x_2751_, v_fst_2743_, v_x_2588_, v___x_2583_, v_compile_2584_, v_logCompileErrors_2585_, v_isMeta_2586_, v___x_2582_, v_numParams_2757_, v___x_2758_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec_ref(v_x_2588_);
if (lean_obj_tag(v___x_2759_) == 0)
{
size_t v_sz_2760_; size_t v___x_2761_; lean_object* v___x_2762_; 
lean_dec_ref(v___x_2759_);
v_sz_2760_ = lean_array_size(v_fst_2743_);
v___x_2761_ = ((size_t)0ULL);
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_2760_, v___x_2761_, v_fst_2743_, v___y_2754_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2771_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2771_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2771_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2767_ = l_Lean_mkAppN(v_x_2587_, v_a_2763_);
lean_dec(v_a_2763_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2767_);
v___x_2769_ = v___x_2765_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref(v_x_2587_);
v_a_2772_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2762_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2762_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_fst_2743_);
lean_dec_ref(v_x_2587_);
v_a_2780_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2759_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2759_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v_val_2736_);
lean_dec_ref(v_x_2588_);
lean_dec_ref(v_x_2587_);
lean_dec_ref(v_expectedType_2581_);
v_a_2843_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2740_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2740_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_dec_ref(v_val_2736_);
lean_dec_ref(v_x_2588_);
lean_dec_ref(v_x_2587_);
lean_dec_ref(v_expectedType_2581_);
return v___x_2737_;
}
}
else
{
lean_dec(v_a_2735_);
lean_dec_ref(v_x_2588_);
lean_dec_ref(v_x_2587_);
v___y_2713_ = v___y_2590_;
v___y_2714_ = v___y_2591_;
v___y_2715_ = v___y_2592_;
v___y_2716_ = v___y_2593_;
goto v___jp_2712_;
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec_ref(v_x_2588_);
lean_dec_ref(v_x_2587_);
lean_dec_ref(v_expectedType_2581_);
lean_dec_ref(v_a_2580_);
v_a_2851_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2734_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2734_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
v___jp_2712_:
{
lean_object* v___x_2717_; lean_object* v_a_2718_; uint8_t v___x_2719_; 
v___x_2717_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2711_, v___y_2715_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref(v___x_2717_);
v___x_2719_ = lean_unbox(v_a_2718_);
lean_dec(v_a_2718_);
if (v___x_2719_ == 0)
{
v___y_2635_ = v___y_2713_;
v___y_2636_ = v___y_2714_;
v___y_2637_ = v___y_2715_;
v___y_2638_ = v___y_2716_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2720_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3);
lean_inc_ref(v_a_2580_);
v___x_2721_ = l_Lean_MessageData_ofExpr(v_a_2580_);
v___x_2722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2711_, v___x_2722_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_dec_ref(v___x_2723_);
v___y_2635_ = v___y_2713_;
v___y_2636_ = v___y_2714_;
v___y_2637_ = v___y_2715_;
v___y_2638_ = v___y_2716_;
goto v___jp_2634_;
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec_ref(v_expectedType_2581_);
lean_dec_ref(v_a_2580_);
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
v___jp_2595_:
{
lean_object* v___x_2600_; 
lean_inc_ref(v___y_2598_);
v___x_2600_ = l_Lean_enableRealizationsForConst(v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; 
v_unused_2608_ = lean_ctor_get(v___x_2600_, 0);
lean_dec(v_unused_2608_);
v___x_2602_ = v___x_2600_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_dec(v___x_2600_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___y_2596_);
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___y_2596_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec_ref(v___y_2596_);
v_a_2609_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2600_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2600_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
v___jp_2617_:
{
if (v_compile_2584_ == 0)
{
v___y_2596_ = v___y_2618_;
v___y_2597_ = v___y_2619_;
v___y_2598_ = v___y_2620_;
v___y_2599_ = v___y_2621_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2622_ = lean_unsigned_to_nat(1u);
v___x_2623_ = lean_mk_empty_array_with_capacity(v___x_2622_);
lean_inc(v___y_2619_);
v___x_2624_ = lean_array_push(v___x_2623_, v___y_2619_);
v___x_2625_ = l_Lean_compileDecls(v___x_2624_, v_logCompileErrors_2585_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_dec_ref(v___x_2625_);
v___y_2596_ = v___y_2618_;
v___y_2597_ = v___y_2619_;
v___y_2598_ = v___y_2620_;
v___y_2599_ = v___y_2621_;
goto v___jp_2595_;
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
v___jp_2634_:
{
lean_object* v_options_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v_options_2639_ = lean_ctor_get(v___y_2637_, 2);
v___x_2640_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2641_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2639_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; 
lean_dec_ref(v_expectedType_2581_);
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v_a_2580_);
return v___x_2642_;
}
else
{
lean_object* v___x_2643_; 
lean_inc(v___y_2638_);
lean_inc_ref(v___y_2637_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc_ref(v_a_2580_);
v___x_2643_ = lean_infer_type(v_a_2580_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2645_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v___x_2643_);
lean_inc_ref(v_expectedType_2581_);
v___x_2645_ = l_Lean_Meta_isExprDefEq(v_expectedType_2581_, v_a_2644_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2696_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2696_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2696_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_unbox(v_a_2646_);
lean_dec(v_a_2646_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v_a_2653_; lean_object* v___x_2654_; 
lean_del_object(v___x_2648_);
v___x_2651_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1));
v___x_2652_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2651_, v___y_2638_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
lean_inc(v_a_2653_);
v___x_2654_ = l_Lean_Meta_mkAuxDefinition(v_a_2653_, v_expectedType_2581_, v_a_2580_, v___x_2582_, v___x_2582_, v___x_2583_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; uint8_t v___x_2656_; lean_object* v___x_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2654_);
v___x_2656_ = 3;
lean_inc(v_a_2653_);
v___x_2657_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(v_a_2653_, v___x_2656_, v___y_2636_, v___y_2638_);
lean_dec_ref(v___x_2657_);
if (v_isMeta_2586_ == 0)
{
v___y_2618_ = v_a_2655_;
v___y_2619_ = v_a_2653_;
v___y_2620_ = v___y_2637_;
v___y_2621_ = v___y_2638_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2658_; lean_object* v_env_2659_; lean_object* v_nextMacroScope_2660_; lean_object* v_ngen_2661_; lean_object* v_auxDeclNGen_2662_; lean_object* v_traceState_2663_; lean_object* v_messages_2664_; lean_object* v_infoState_2665_; lean_object* v_snapshotTasks_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2691_; 
v___x_2658_ = lean_st_ref_take(v___y_2638_);
v_env_2659_ = lean_ctor_get(v___x_2658_, 0);
v_nextMacroScope_2660_ = lean_ctor_get(v___x_2658_, 1);
v_ngen_2661_ = lean_ctor_get(v___x_2658_, 2);
v_auxDeclNGen_2662_ = lean_ctor_get(v___x_2658_, 3);
v_traceState_2663_ = lean_ctor_get(v___x_2658_, 4);
v_messages_2664_ = lean_ctor_get(v___x_2658_, 6);
v_infoState_2665_ = lean_ctor_get(v___x_2658_, 7);
v_snapshotTasks_2666_ = lean_ctor_get(v___x_2658_, 8);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; 
v_unused_2692_ = lean_ctor_get(v___x_2658_, 5);
lean_dec(v_unused_2692_);
v___x_2668_ = v___x_2658_;
v_isShared_2669_ = v_isSharedCheck_2691_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_snapshotTasks_2666_);
lean_inc(v_infoState_2665_);
lean_inc(v_messages_2664_);
lean_inc(v_traceState_2663_);
lean_inc(v_auxDeclNGen_2662_);
lean_inc(v_ngen_2661_);
lean_inc(v_nextMacroScope_2660_);
lean_inc(v_env_2659_);
lean_dec(v___x_2658_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2691_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_inc(v_a_2653_);
v___x_2670_ = l_Lean_markMeta(v_env_2659_, v_a_2653_);
v___x_2671_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 5, v___x_2671_);
lean_ctor_set(v___x_2668_, 0, v___x_2670_);
v___x_2673_ = v___x_2668_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_nextMacroScope_2660_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_ngen_2661_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_auxDeclNGen_2662_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v_traceState_2663_);
lean_ctor_set(v_reuseFailAlloc_2690_, 5, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2690_, 6, v_messages_2664_);
lean_ctor_set(v_reuseFailAlloc_2690_, 7, v_infoState_2665_);
lean_ctor_set(v_reuseFailAlloc_2690_, 8, v_snapshotTasks_2666_);
v___x_2673_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v_mctx_2676_; lean_object* v_zetaDeltaFVarIds_2677_; lean_object* v_postponed_2678_; lean_object* v_diag_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2688_; 
v___x_2674_ = lean_st_ref_set(v___y_2638_, v___x_2673_);
v___x_2675_ = lean_st_ref_take(v___y_2636_);
v_mctx_2676_ = lean_ctor_get(v___x_2675_, 0);
v_zetaDeltaFVarIds_2677_ = lean_ctor_get(v___x_2675_, 2);
v_postponed_2678_ = lean_ctor_get(v___x_2675_, 3);
v_diag_2679_ = lean_ctor_get(v___x_2675_, 4);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v___x_2675_, 1);
lean_dec(v_unused_2689_);
v___x_2681_ = v___x_2675_;
v_isShared_2682_ = v_isSharedCheck_2688_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_diag_2679_);
lean_inc(v_postponed_2678_);
lean_inc(v_zetaDeltaFVarIds_2677_);
lean_inc(v_mctx_2676_);
lean_dec(v___x_2675_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2688_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2683_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_mctx_2676_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_zetaDeltaFVarIds_2677_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_postponed_2678_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_diag_2679_);
v___x_2685_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_st_ref_set(v___y_2636_, v___x_2685_);
v___y_2618_ = v_a_2655_;
v___y_2619_ = v_a_2653_;
v___y_2620_ = v___y_2637_;
v___y_2621_ = v___y_2638_;
goto v___jp_2617_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2653_);
return v___x_2654_;
}
}
else
{
lean_object* v___x_2694_; 
lean_dec_ref(v_expectedType_2581_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_a_2580_);
v___x_2694_ = v___x_2648_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2580_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v_expectedType_2581_);
lean_dec_ref(v_a_2580_);
v_a_2697_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2645_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2645_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2581_);
lean_dec_ref(v_a_2580_);
return v___x_2643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__1(lean_object* v_expectedType_2859_, lean_object* v_inst_2860_, uint8_t v___x_2861_, uint8_t v_hasTrace_2862_, uint8_t v_compile_2863_, uint8_t v_logCompileErrors_2864_, uint8_t v_isMeta_2865_, lean_object* v_____r_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v___x_2872_; 
lean_inc_ref(v_expectedType_2859_);
v___x_2872_ = l_Lean_Meta_isProp(v_expectedType_2859_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2894_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2894_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2894_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
uint8_t v___x_2877_; 
v___x_2877_ = lean_unbox(v_a_2873_);
lean_dec(v_a_2873_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_del_object(v___x_2875_);
lean_inc(v___y_2870_);
lean_inc_ref(v___y_2869_);
lean_inc(v___y_2868_);
lean_inc_ref(v___y_2867_);
v___x_2878_ = lean_whnf(v_inst_2860_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v_dummy_2880_; lean_object* v_nargs_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v___x_2878_);
v_dummy_2880_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_2881_ = l_Lean_Expr_getAppNumArgs(v_a_2879_);
lean_inc(v_nargs_2881_);
v___x_2882_ = lean_mk_array(v_nargs_2881_, v_dummy_2880_);
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = lean_nat_sub(v_nargs_2881_, v___x_2883_);
lean_dec(v_nargs_2881_);
lean_inc(v_a_2879_);
v___x_2885_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(v_a_2879_, v_expectedType_2859_, v___x_2861_, v_hasTrace_2862_, v_compile_2863_, v_logCompileErrors_2864_, v_isMeta_2865_, v_a_2879_, v___x_2882_, v___x_2884_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
return v___x_2885_;
}
else
{
lean_dec_ref(v_expectedType_2859_);
return v___x_2878_;
}
}
else
{
lean_object* v_options_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_options_2886_ = lean_ctor_get(v___y_2869_, 2);
v___x_2887_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2888_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2886_, v___x_2887_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2890_; 
lean_dec_ref(v_expectedType_2859_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v_inst_2860_);
v___x_2890_ = v___x_2875_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_inst_2860_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
lean_del_object(v___x_2875_);
v___x_2892_ = lean_box(0);
v___x_2893_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_2859_, v_inst_2860_, v_hasTrace_2862_, v___x_2892_, v_hasTrace_2862_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v_inst_2860_);
lean_dec_ref(v_expectedType_2859_);
v_a_2895_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2872_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2872_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(lean_object* v_upperBound_2903_, lean_object* v_fst_2904_, lean_object* v_args_2905_, uint8_t v___x_2906_, uint8_t v_compile_2907_, uint8_t v_logCompileErrors_2908_, uint8_t v_isMeta_2909_, lean_object* v_a_2910_, lean_object* v_b_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_a_2918_; lean_object* v___y_2923_; uint8_t v___x_2942_; 
v___x_2942_ = lean_nat_dec_lt(v_a_2910_, v_upperBound_2903_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec(v_a_2910_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_b_2911_);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_array_fget_borrowed(v_fst_2904_, v_a_2910_);
v___x_2945_ = l_Lean_Expr_mvarId_x21(v___x_2944_);
lean_inc(v___x_2945_);
v___x_2946_ = l_Lean_MVarId_getDecl(v___x_2945_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v_type_2948_; lean_object* v___x_2949_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref(v___x_2946_);
v_type_2948_ = lean_ctor_get(v_a_2947_, 2);
lean_inc_ref(v_type_2948_);
lean_dec(v_a_2947_);
v___x_2949_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2948_, v___y_2913_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2949_);
lean_inc(v_a_2950_);
v___x_2951_ = l_Lean_Meta_isProp(v_a_2950_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v_cls_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = lean_box(0);
v_cls_2954_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_2955_ = lean_array_fget_borrowed(v_args_2905_, v_a_2910_);
v___x_2956_ = lean_unbox(v_a_2952_);
lean_dec(v_a_2952_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
lean_inc(v_a_2950_);
v___x_2957_ = l_Lean_Meta_isClass_x3f(v_a_2950_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_3091_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_3091_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_3091_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
if (lean_obj_tag(v_a_2958_) == 0)
{
lean_del_object(v___x_2960_);
goto v___jp_2962_;
}
else
{
lean_dec_ref(v_a_2958_);
if (v___x_2906_ == 0)
{
lean_del_object(v___x_2960_);
goto v___jp_2962_;
}
else
{
lean_object* v_options_3052_; lean_object* v_a_3054_; lean_object* v___y_3057_; uint8_t v___y_3058_; lean_object* v_a_3063_; lean_object* v___y_3067_; lean_object* v___x_3071_; uint8_t v___x_3072_; 
v_options_3052_ = lean_ctor_get(v___y_2914_, 2);
v___x_3071_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3072_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3052_, v___x_3071_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; 
lean_del_object(v___x_2960_);
lean_inc(v___x_2955_);
v___x_3073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_2955_, v_a_2950_, v_compile_2907_, v_logCompileErrors_2908_, v_isMeta_2909_, v___x_2945_, v___x_2953_, v___x_2953_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___y_2923_ = v___x_3073_;
goto v___jp_2922_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_box(0);
lean_inc(v_a_2950_);
v___x_3075_ = l_Lean_Meta_trySynthInstance(v_a_2950_, v___x_3074_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref(v___x_3075_);
if (lean_obj_tag(v_a_3076_) == 1)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; 
v_a_3077_ = lean_ctor_get(v_a_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref(v_a_3076_);
v___x_3078_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2954_, v___y_2914_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; uint8_t v___x_3080_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref(v___x_3078_);
v___x_3080_ = lean_unbox(v_a_3079_);
lean_dec(v_a_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; 
lean_inc(v___x_2945_);
v___x_3081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_2945_, v_a_3077_, v___x_2953_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___y_3067_ = v___x_3081_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3082_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__1);
lean_inc(v_a_3077_);
v___x_3083_ = l_Lean_MessageData_ofExpr(v_a_3077_);
v___x_3084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2954_, v___x_3084_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3087_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref(v___x_3085_);
lean_inc(v___x_2945_);
v___x_3087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__2(v___x_2945_, v_a_3077_, v_a_3086_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___y_3067_ = v___x_3087_;
goto v___jp_3066_;
}
else
{
lean_object* v_a_3088_; 
lean_dec(v_a_3077_);
v_a_3088_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3088_);
lean_dec_ref(v___x_3085_);
v_a_3063_ = v_a_3088_;
goto v___jp_3062_;
}
}
}
else
{
lean_object* v_a_3089_; 
lean_dec(v_a_3077_);
v_a_3089_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3089_);
lean_dec_ref(v___x_3078_);
v_a_3063_ = v_a_3089_;
goto v___jp_3062_;
}
}
else
{
lean_dec(v_a_3076_);
lean_del_object(v___x_2960_);
v_a_3054_ = v___x_2953_;
goto v___jp_3053_;
}
}
else
{
lean_object* v_a_3090_; 
v_a_3090_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3090_);
lean_dec_ref(v___x_3075_);
v_a_3063_ = v_a_3090_;
goto v___jp_3062_;
}
}
v___jp_3053_:
{
lean_object* v___x_3055_; 
lean_inc(v___x_2955_);
v___x_3055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_2955_, v_a_2950_, v_compile_2907_, v_logCompileErrors_2908_, v_isMeta_2909_, v___x_2945_, v___x_2953_, v_a_3054_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___y_2923_ = v___x_3055_;
goto v___jp_2922_;
}
v___jp_3056_:
{
if (v___y_3058_ == 0)
{
lean_dec_ref(v___y_3057_);
lean_del_object(v___x_2960_);
v_a_3054_ = v___x_2953_;
goto v___jp_3053_;
}
else
{
lean_object* v___x_3060_; 
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set_tag(v___x_2960_, 1);
lean_ctor_set(v___x_2960_, 0, v___y_3057_);
v___x_3060_ = v___x_2960_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___y_3057_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
v___jp_3062_:
{
uint8_t v___x_3064_; 
v___x_3064_ = l_Lean_Exception_isInterrupt(v_a_3063_);
if (v___x_3064_ == 0)
{
uint8_t v___x_3065_; 
lean_inc_ref(v_a_3063_);
v___x_3065_ = l_Lean_Exception_isRuntime(v_a_3063_);
v___y_3057_ = v_a_3063_;
v___y_3058_ = v___x_3065_;
goto v___jp_3056_;
}
else
{
v___y_3057_ = v_a_3063_;
v___y_3058_ = v___x_3064_;
goto v___jp_3056_;
}
}
v___jp_3066_:
{
if (lean_obj_tag(v___y_3067_) == 0)
{
lean_object* v_a_3068_; 
lean_del_object(v___x_2960_);
v_a_3068_ = lean_ctor_get(v___y_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___y_3067_);
if (lean_obj_tag(v_a_3068_) == 0)
{
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
v_a_2918_ = v___x_2953_;
goto v___jp_2917_;
}
else
{
lean_object* v_a_3069_; 
v_a_3069_ = lean_ctor_get(v_a_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref(v_a_3068_);
v_a_3054_ = v_a_3069_;
goto v___jp_3053_;
}
}
else
{
lean_object* v_a_3070_; 
v_a_3070_ = lean_ctor_get(v___y_3067_, 0);
lean_inc(v_a_3070_);
lean_dec_ref(v___y_3067_);
v_a_3063_ = v_a_3070_;
goto v___jp_3062_;
}
}
}
}
v___jp_2962_:
{
lean_object* v_options_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v_options_2963_ = lean_ctor_get(v___y_2914_, 2);
v___x_2964_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2965_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_2963_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
lean_dec(v_a_2950_);
lean_inc(v___x_2955_);
v___x_2966_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2945_, v___x_2955_, v___y_2913_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_dec_ref(v___x_2966_);
v_a_2918_ = v___x_2953_;
goto v___jp_2917_;
}
else
{
lean_dec(v_a_2910_);
return v___x_2966_;
}
}
else
{
lean_object* v___x_2967_; 
lean_inc(v___y_2915_);
lean_inc_ref(v___y_2914_);
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2912_);
lean_inc(v___x_2955_);
v___x_2967_ = lean_infer_type(v___x_2955_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref(v___x_2967_);
lean_inc(v_a_2950_);
v___x_2969_ = l_Lean_Meta_isExprDefEq(v_a_2950_, v_a_2968_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; uint8_t v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = lean_unbox(v_a_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1));
v___x_2973_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_2972_, v___y_2915_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; uint8_t v___x_2975_; uint8_t v___x_2976_; lean_object* v___x_2977_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref(v___x_2973_);
v___x_2975_ = lean_unbox(v_a_2970_);
v___x_2976_ = lean_unbox(v_a_2970_);
lean_dec(v_a_2970_);
lean_inc(v___x_2955_);
lean_inc(v_a_2974_);
v___x_2977_ = l_Lean_Meta_mkAuxDefinition(v_a_2974_, v_a_2950_, v___x_2955_, v___x_2975_, v___x_2976_, v___x_2906_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2945_, v_a_2978_, v___y_2913_);
if (lean_obj_tag(v___x_2979_) == 0)
{
uint8_t v___x_2980_; lean_object* v___x_2981_; 
lean_dec_ref(v___x_2979_);
v___x_2980_ = 0;
lean_inc(v_a_2974_);
v___x_2981_ = l_Lean_Meta_setInlineAttribute(v_a_2974_, v___x_2980_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_dec_ref(v___x_2981_);
if (v_isMeta_2909_ == 0)
{
lean_object* v___x_2982_; 
v___x_2982_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_2974_, v___x_2953_, v_compile_2907_, v_logCompileErrors_2908_, v___x_2953_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___y_2923_ = v___x_2982_;
goto v___jp_2922_;
}
else
{
lean_object* v___x_2983_; lean_object* v_env_2984_; lean_object* v_nextMacroScope_2985_; lean_object* v_ngen_2986_; lean_object* v_auxDeclNGen_2987_; lean_object* v_traceState_2988_; lean_object* v_messages_2989_; lean_object* v_infoState_2990_; lean_object* v_snapshotTasks_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3017_; 
v___x_2983_ = lean_st_ref_take(v___y_2915_);
v_env_2984_ = lean_ctor_get(v___x_2983_, 0);
v_nextMacroScope_2985_ = lean_ctor_get(v___x_2983_, 1);
v_ngen_2986_ = lean_ctor_get(v___x_2983_, 2);
v_auxDeclNGen_2987_ = lean_ctor_get(v___x_2983_, 3);
v_traceState_2988_ = lean_ctor_get(v___x_2983_, 4);
v_messages_2989_ = lean_ctor_get(v___x_2983_, 6);
v_infoState_2990_ = lean_ctor_get(v___x_2983_, 7);
v_snapshotTasks_2991_ = lean_ctor_get(v___x_2983_, 8);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_2983_, 5);
lean_dec(v_unused_3018_);
v___x_2993_ = v___x_2983_;
v_isShared_2994_ = v_isSharedCheck_3017_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_snapshotTasks_2991_);
lean_inc(v_infoState_2990_);
lean_inc(v_messages_2989_);
lean_inc(v_traceState_2988_);
lean_inc(v_auxDeclNGen_2987_);
lean_inc(v_ngen_2986_);
lean_inc(v_nextMacroScope_2985_);
lean_inc(v_env_2984_);
lean_dec(v___x_2983_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3017_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
lean_inc(v_a_2974_);
v___x_2995_ = l_Lean_markMeta(v_env_2984_, v_a_2974_);
v___x_2996_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 5, v___x_2996_);
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2998_ = v___x_2993_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_nextMacroScope_2985_);
lean_ctor_set(v_reuseFailAlloc_3016_, 2, v_ngen_2986_);
lean_ctor_set(v_reuseFailAlloc_3016_, 3, v_auxDeclNGen_2987_);
lean_ctor_set(v_reuseFailAlloc_3016_, 4, v_traceState_2988_);
lean_ctor_set(v_reuseFailAlloc_3016_, 5, v___x_2996_);
lean_ctor_set(v_reuseFailAlloc_3016_, 6, v_messages_2989_);
lean_ctor_set(v_reuseFailAlloc_3016_, 7, v_infoState_2990_);
lean_ctor_set(v_reuseFailAlloc_3016_, 8, v_snapshotTasks_2991_);
v___x_2998_ = v_reuseFailAlloc_3016_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_mctx_3001_; lean_object* v_zetaDeltaFVarIds_3002_; lean_object* v_postponed_3003_; lean_object* v_diag_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3014_; 
v___x_2999_ = lean_st_ref_set(v___y_2915_, v___x_2998_);
v___x_3000_ = lean_st_ref_take(v___y_2913_);
v_mctx_3001_ = lean_ctor_get(v___x_3000_, 0);
v_zetaDeltaFVarIds_3002_ = lean_ctor_get(v___x_3000_, 2);
v_postponed_3003_ = lean_ctor_get(v___x_3000_, 3);
v_diag_3004_ = lean_ctor_get(v___x_3000_, 4);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v___x_3000_, 1);
lean_dec(v_unused_3015_);
v___x_3006_ = v___x_3000_;
v_isShared_3007_ = v_isSharedCheck_3014_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_diag_3004_);
lean_inc(v_postponed_3003_);
lean_inc(v_zetaDeltaFVarIds_3002_);
lean_inc(v_mctx_3001_);
lean_dec(v___x_3000_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3014_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3008_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___x_3008_);
v___x_3010_ = v___x_3006_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_mctx_3001_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_zetaDeltaFVarIds_3002_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_postponed_3003_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_diag_3004_);
v___x_3010_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_st_ref_set(v___y_2913_, v___x_3010_);
v___x_3012_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__0(v_a_2974_, v___x_2953_, v_compile_2907_, v_logCompileErrors_2908_, v___x_2953_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___y_2923_ = v___x_3012_;
goto v___jp_2922_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2974_);
lean_dec(v_a_2910_);
return v___x_2981_;
}
}
else
{
lean_dec(v_a_2974_);
lean_dec(v_a_2910_);
return v___x_2979_;
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_a_2974_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3019_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2977_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2977_);
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
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_a_2970_);
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3027_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2973_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2973_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v___x_3035_; 
lean_dec(v_a_2970_);
lean_dec(v_a_2950_);
lean_inc(v___x_2955_);
v___x_3035_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2945_, v___x_2955_, v___y_2913_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref(v___x_3035_);
v_a_2918_ = v___x_2953_;
goto v___jp_2917_;
}
else
{
lean_dec(v_a_2910_);
return v___x_3035_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3036_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_2969_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_2969_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3044_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2967_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_2967_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3092_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_2957_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_2957_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v___x_3100_; 
lean_inc(v___y_2915_);
lean_inc_ref(v___y_2914_);
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2912_);
lean_inc(v___x_2955_);
v___x_3100_ = lean_infer_type(v___x_2955_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref(v___x_3100_);
lean_inc(v_a_3101_);
lean_inc(v_a_2950_);
v___x_3102_ = l_Lean_Meta_isExprDefEq(v_a_2950_, v_a_3101_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; uint8_t v___x_3104_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref(v___x_3102_);
v___x_3104_ = lean_unbox(v_a_3103_);
lean_dec(v_a_3103_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_2954_, v___y_2914_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; uint8_t v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v___x_3105_);
v___x_3107_ = lean_unbox(v_a_3106_);
lean_dec(v_a_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_dec(v_a_3101_);
lean_inc(v___x_2955_);
v___x_3108_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_2950_, v___x_2955_, v___x_2906_, v___x_2945_, v___x_2953_, v___x_2953_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___y_2923_ = v___x_3108_;
goto v___jp_2922_;
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3109_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__3);
lean_inc(v_a_2910_);
v___x_3110_ = l_Nat_reprFast(v_a_2910_);
v___x_3111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
v___x_3112_ = l_Lean_MessageData_ofFormat(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3109_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__5);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
lean_inc(v_a_2950_);
v___x_3116_ = l_Lean_MessageData_ofExpr(v_a_2950_);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__7);
v___x_3119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = l_Lean_MessageData_ofExpr(v_a_3101_);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___closed__9);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
lean_inc(v___x_2955_);
v___x_3124_ = l_Lean_MessageData_ofExpr(v___x_2955_);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_2954_, v___x_3125_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3128_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
lean_inc(v___x_2955_);
v___x_3128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__3(v_a_2950_, v___x_2955_, v___x_2906_, v___x_2945_, v___x_2953_, v_a_3127_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___y_2923_ = v___x_3128_;
goto v___jp_2922_;
}
else
{
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
return v___x_3126_;
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_a_3101_);
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3129_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3105_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3105_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v___x_3137_; 
lean_dec(v_a_3101_);
lean_dec(v_a_2950_);
lean_inc(v___x_2955_);
v___x_3137_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2945_, v___x_2955_, v___y_2913_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_dec_ref(v___x_3137_);
v_a_2918_ = v___x_2953_;
goto v___jp_2917_;
}
else
{
lean_dec(v_a_2910_);
return v___x_3137_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_a_3101_);
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3138_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3102_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3102_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
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
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3146_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3100_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3100_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_a_2950_);
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3154_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_2951_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_2951_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3162_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_2949_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_2949_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v___x_2945_);
lean_dec(v_a_2910_);
v_a_3170_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_2946_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_2946_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
v___jp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_unsigned_to_nat(1u);
v___x_2920_ = lean_nat_add(v_a_2910_, v___x_2919_);
lean_dec(v_a_2910_);
v_a_2910_ = v___x_2920_;
v_b_2911_ = v_a_2918_;
goto _start;
}
v___jp_2922_:
{
if (lean_obj_tag(v___y_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2933_; 
v_a_2924_ = lean_ctor_get(v___y_2923_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___y_2923_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2926_ = v___y_2923_;
v_isShared_2927_ = v_isSharedCheck_2933_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___y_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2933_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
if (lean_obj_tag(v_a_2924_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; 
lean_dec(v_a_2910_);
v_a_2928_ = lean_ctor_get(v_a_2924_, 0);
lean_inc(v_a_2928_);
lean_dec_ref(v_a_2924_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v_a_2928_);
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
else
{
lean_object* v_a_2932_; 
lean_del_object(v___x_2926_);
v_a_2932_ = lean_ctor_get(v_a_2924_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v_a_2924_);
v_a_2918_ = v_a_2932_;
goto v___jp_2917_;
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_a_2910_);
v_a_2934_ = lean_ctor_get(v___y_2923_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___y_2923_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___y_2923_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___y_2923_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15(lean_object* v_a_3178_, lean_object* v_expectedType_3179_, uint8_t v___x_3180_, uint8_t v_compile_3181_, uint8_t v_logCompileErrors_3182_, uint8_t v_isMeta_3183_, lean_object* v_x_3184_, lean_object* v_x_3185_, lean_object* v_x_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; 
if (lean_obj_tag(v_x_3184_) == 5)
{
lean_object* v_fn_3304_; lean_object* v_arg_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_fn_3304_ = lean_ctor_get(v_x_3184_, 0);
lean_inc_ref(v_fn_3304_);
v_arg_3305_ = lean_ctor_get(v_x_3184_, 1);
lean_inc_ref(v_arg_3305_);
lean_dec_ref(v_x_3184_);
v___x_3306_ = lean_array_set(v_x_3185_, v_x_3186_, v_arg_3305_);
v___x_3307_ = lean_unsigned_to_nat(1u);
v___x_3308_ = lean_nat_sub(v_x_3186_, v___x_3307_);
lean_dec(v_x_3186_);
v_x_3184_ = v_fn_3304_;
v_x_3185_ = v___x_3306_;
v_x_3186_ = v___x_3308_;
goto _start;
}
else
{
lean_object* v_cls_3310_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___x_3331_; 
lean_dec(v_x_3186_);
v_cls_3310_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_3331_ = l_Lean_Expr_constName_x3f(v_x_3184_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_x_3184_);
v___y_3312_ = v___y_3187_;
v___y_3313_ = v___y_3188_;
v___y_3314_ = v___y_3189_;
v___y_3315_ = v___y_3190_;
goto v___jp_3311_;
}
else
{
lean_object* v_val_3332_; lean_object* v___x_3333_; 
v_val_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_val_3332_);
lean_dec_ref(v___x_3331_);
v___x_3333_ = l_Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5(v_val_3332_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref(v___x_3333_);
if (lean_obj_tag(v_a_3334_) == 6)
{
lean_object* v_val_3335_; lean_object* v___x_3336_; 
lean_dec_ref(v_a_3178_);
v_val_3335_ = lean_ctor_get(v_a_3334_, 0);
lean_inc_ref(v_val_3335_);
lean_dec_ref(v_a_3334_);
lean_inc(v___y_3190_);
lean_inc_ref(v___y_3189_);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc_ref(v_x_3184_);
v___x_3336_ = lean_infer_type(v_x_3184_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
lean_dec_ref(v___x_3336_);
v___x_3338_ = 0;
v___x_3339_ = l_Lean_Meta_forallMetaTelescope(v_a_3337_, v___x_3338_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v_snd_3341_; lean_object* v_fst_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3442_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref(v___x_3339_);
v_snd_3341_ = lean_ctor_get(v_a_3340_, 1);
v_fst_3342_ = lean_ctor_get(v_a_3340_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_a_3340_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3344_ = v_a_3340_;
v_isShared_3345_ = v_isSharedCheck_3442_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snd_3341_);
lean_inc(v_fst_3342_);
lean_dec(v_a_3340_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3442_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_snd_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3440_; 
v_snd_3346_ = lean_ctor_get(v_snd_3341_, 1);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_snd_3341_);
if (v_isSharedCheck_3440_ == 0)
{
lean_object* v_unused_3441_; 
v_unused_3441_ = lean_ctor_get(v_snd_3341_, 0);
lean_dec(v_unused_3441_);
v___x_3348_ = v_snd_3341_;
v_isShared_3349_ = v_isSharedCheck_3440_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_snd_3346_);
lean_dec(v_snd_3341_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3440_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3350_ = lean_array_get_size(v_x_3185_);
v___x_3387_ = lean_array_get_size(v_fst_3342_);
v___x_3388_ = lean_nat_dec_eq(v___x_3350_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
lean_dec(v_snd_3346_);
lean_dec(v_fst_3342_);
lean_dec_ref(v_val_3335_);
lean_dec_ref(v_expectedType_3179_);
v___x_3389_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__5);
v___x_3390_ = l_Lean_MessageData_ofExpr(v_x_3184_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set_tag(v___x_3348_, 7);
lean_ctor_set(v___x_3348_, 1, v___x_3390_);
lean_ctor_set(v___x_3348_, 0, v___x_3389_);
v___x_3392_ = v___x_3348_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___x_3393_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__7);
if (v_isShared_3345_ == 0)
{
lean_ctor_set_tag(v___x_3344_, 7);
lean_ctor_set(v___x_3344_, 1, v___x_3393_);
lean_ctor_set(v___x_3344_, 0, v___x_3392_);
v___x_3395_ = v___x_3344_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3396_ = lean_array_to_list(v_x_3185_);
v___x_3397_ = lean_box(0);
v___x_3398_ = l_List_mapTR_loop___at___00Lean_Meta_normalizeInstance_spec__9(v___x_3396_, v___x_3397_);
v___x_3399_ = l_Lean_MessageData_ofList(v___x_3398_);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3395_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_3400_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
return v___x_3401_;
}
}
}
else
{
lean_object* v___x_3404_; 
lean_inc_ref(v_expectedType_3179_);
v___x_3404_ = l_Lean_Meta_isExprDefEq(v_expectedType_3179_, v_snd_3346_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; uint8_t v___x_3406_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref(v___x_3404_);
v___x_3406_ = lean_unbox(v_a_3405_);
if (v___x_3406_ == 0)
{
lean_object* v_toConstantVal_3407_; lean_object* v_name_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
lean_dec(v_fst_3342_);
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_x_3184_);
v_toConstantVal_3407_ = lean_ctor_get(v_val_3335_, 0);
lean_inc_ref(v_toConstantVal_3407_);
lean_dec_ref(v_val_3335_);
v_name_3408_ = lean_ctor_get(v_toConstantVal_3407_, 0);
lean_inc(v_name_3408_);
lean_dec_ref(v_toConstantVal_3407_);
v___x_3409_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__9);
v___x_3410_ = l_Lean_MessageData_ofExpr(v_expectedType_3179_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set_tag(v___x_3348_, 7);
lean_ctor_set(v___x_3348_, 1, v___x_3410_);
lean_ctor_set(v___x_3348_, 0, v___x_3409_);
v___x_3412_ = v___x_3348_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__11);
if (v_isShared_3345_ == 0)
{
lean_ctor_set_tag(v___x_3344_, 7);
lean_ctor_set(v___x_3344_, 1, v___x_3413_);
lean_ctor_set(v___x_3344_, 0, v___x_3412_);
v___x_3415_ = v___x_3344_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
uint8_t v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
v___x_3416_ = lean_unbox(v_a_3405_);
lean_dec(v_a_3405_);
v___x_3417_ = l_Lean_MessageData_ofConstName(v_name_3408_, v___x_3416_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3415_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg___closed__3);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v___x_3420_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
else
{
lean_dec(v_a_3405_);
lean_del_object(v___x_3348_);
lean_del_object(v___x_3344_);
lean_dec_ref(v_expectedType_3179_);
v___y_3352_ = v___y_3187_;
v___y_3353_ = v___y_3188_;
v___y_3354_ = v___y_3189_;
v___y_3355_ = v___y_3190_;
goto v___jp_3351_;
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_del_object(v___x_3348_);
lean_del_object(v___x_3344_);
lean_dec(v_fst_3342_);
lean_dec_ref(v_val_3335_);
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_x_3184_);
lean_dec_ref(v_expectedType_3179_);
v_a_3432_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3404_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3404_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
v___jp_3351_:
{
lean_object* v_numParams_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_numParams_3356_ = lean_ctor_get(v_val_3335_, 3);
lean_inc(v_numParams_3356_);
lean_dec_ref(v_val_3335_);
v___x_3357_ = lean_box(0);
v___x_3358_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(v___x_3350_, v_fst_3342_, v_x_3185_, v___x_3180_, v_compile_3181_, v_logCompileErrors_3182_, v_isMeta_3183_, v_numParams_3356_, v___x_3357_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec_ref(v_x_3185_);
if (lean_obj_tag(v___x_3358_) == 0)
{
size_t v_sz_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
lean_dec_ref(v___x_3358_);
v_sz_3359_ = lean_array_size(v_fst_3342_);
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_3359_, v___x_3360_, v_fst_3342_, v___y_3353_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3370_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3370_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3370_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = l_Lean_mkAppN(v_x_3184_, v_a_3362_);
lean_dec(v_a_3362_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3366_);
v___x_3368_ = v___x_3364_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v_x_3184_);
v_a_3371_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3361_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3361_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_fst_3342_);
lean_dec_ref(v_x_3184_);
v_a_3379_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3358_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3358_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec_ref(v_val_3335_);
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_x_3184_);
lean_dec_ref(v_expectedType_3179_);
v_a_3443_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3339_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3339_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
else
{
lean_dec_ref(v_val_3335_);
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_x_3184_);
lean_dec_ref(v_expectedType_3179_);
return v___x_3336_;
}
}
else
{
lean_dec(v_a_3334_);
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_x_3184_);
v___y_3312_ = v___y_3187_;
v___y_3313_ = v___y_3188_;
v___y_3314_ = v___y_3189_;
v___y_3315_ = v___y_3190_;
goto v___jp_3311_;
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_x_3184_);
lean_dec_ref(v_expectedType_3179_);
lean_dec_ref(v_a_3178_);
v_a_3451_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3333_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3333_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
v___jp_3311_:
{
lean_object* v___x_3316_; lean_object* v_a_3317_; uint8_t v___x_3318_; 
v___x_3316_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3310_, v___y_3314_);
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3316_);
v___x_3318_ = lean_unbox(v_a_3317_);
lean_dec(v_a_3317_);
if (v___x_3318_ == 0)
{
v___y_3232_ = v___y_3312_;
v___y_3233_ = v___y_3313_;
v___y_3234_ = v___y_3314_;
v___y_3235_ = v___y_3315_;
goto v___jp_3231_;
}
else
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3319_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__3);
lean_inc_ref(v_a_3178_);
v___x_3320_ = l_Lean_MessageData_ofExpr(v_a_3178_);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3310_, v___x_3321_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_dec_ref(v___x_3322_);
v___y_3232_ = v___y_3312_;
v___y_3233_ = v___y_3313_;
v___y_3234_ = v___y_3314_;
v___y_3235_ = v___y_3315_;
goto v___jp_3231_;
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec_ref(v_expectedType_3179_);
lean_dec_ref(v_a_3178_);
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
}
v___jp_3192_:
{
lean_object* v___x_3197_; 
lean_inc_ref(v___y_3195_);
v___x_3197_ = l_Lean_enableRealizationsForConst(v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; 
v_unused_3205_ = lean_ctor_get(v___x_3197_, 0);
lean_dec(v_unused_3205_);
v___x_3199_ = v___x_3197_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_dec(v___x_3197_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___y_3193_);
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___y_3193_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v___y_3193_);
v_a_3206_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3197_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3197_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
v___jp_3214_:
{
if (v_compile_3181_ == 0)
{
v___y_3193_ = v___y_3216_;
v___y_3194_ = v___y_3215_;
v___y_3195_ = v___y_3217_;
v___y_3196_ = v___y_3218_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3219_ = lean_unsigned_to_nat(1u);
v___x_3220_ = lean_mk_empty_array_with_capacity(v___x_3219_);
lean_inc(v___y_3215_);
v___x_3221_ = lean_array_push(v___x_3220_, v___y_3215_);
v___x_3222_ = l_Lean_compileDecls(v___x_3221_, v_logCompileErrors_3182_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_dec_ref(v___x_3222_);
v___y_3193_ = v___y_3216_;
v___y_3194_ = v___y_3215_;
v___y_3195_ = v___y_3217_;
v___y_3196_ = v___y_3218_;
goto v___jp_3192_;
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
}
v___jp_3231_:
{
lean_object* v_options_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v_options_3236_ = lean_ctor_get(v___y_3234_, 2);
v___x_3237_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3238_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3236_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
lean_dec_ref(v_expectedType_3179_);
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_a_3178_);
return v___x_3239_;
}
else
{
lean_object* v___x_3240_; 
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3234_);
lean_inc(v___y_3233_);
lean_inc_ref(v___y_3232_);
lean_inc_ref(v_a_3178_);
v___x_3240_ = lean_infer_type(v_a_3178_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3242_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref(v___x_3240_);
lean_inc_ref(v_expectedType_3179_);
v___x_3242_ = l_Lean_Meta_isExprDefEq(v_expectedType_3179_, v_a_3241_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3295_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3295_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3295_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_unbox(v_a_3243_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v_a_3250_; uint8_t v___x_3251_; uint8_t v___x_3252_; lean_object* v___x_3253_; 
lean_del_object(v___x_3245_);
v___x_3248_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___closed__1));
v___x_3249_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_normalizeInstance_spec__1___redArg(v___x_3248_, v___y_3235_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = lean_unbox(v_a_3243_);
v___x_3252_ = lean_unbox(v_a_3243_);
lean_dec(v_a_3243_);
lean_inc(v_a_3250_);
v___x_3253_ = l_Lean_Meta_mkAuxDefinition(v_a_3250_, v_expectedType_3179_, v_a_3178_, v___x_3251_, v___x_3252_, v___x_3180_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___x_3253_);
v___x_3255_ = 3;
lean_inc(v_a_3250_);
v___x_3256_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg(v_a_3250_, v___x_3255_, v___y_3233_, v___y_3235_);
lean_dec_ref(v___x_3256_);
if (v_isMeta_3183_ == 0)
{
v___y_3215_ = v_a_3250_;
v___y_3216_ = v_a_3254_;
v___y_3217_ = v___y_3234_;
v___y_3218_ = v___y_3235_;
goto v___jp_3214_;
}
else
{
lean_object* v___x_3257_; lean_object* v_env_3258_; lean_object* v_nextMacroScope_3259_; lean_object* v_ngen_3260_; lean_object* v_auxDeclNGen_3261_; lean_object* v_traceState_3262_; lean_object* v_messages_3263_; lean_object* v_infoState_3264_; lean_object* v_snapshotTasks_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3290_; 
v___x_3257_ = lean_st_ref_take(v___y_3235_);
v_env_3258_ = lean_ctor_get(v___x_3257_, 0);
v_nextMacroScope_3259_ = lean_ctor_get(v___x_3257_, 1);
v_ngen_3260_ = lean_ctor_get(v___x_3257_, 2);
v_auxDeclNGen_3261_ = lean_ctor_get(v___x_3257_, 3);
v_traceState_3262_ = lean_ctor_get(v___x_3257_, 4);
v_messages_3263_ = lean_ctor_get(v___x_3257_, 6);
v_infoState_3264_ = lean_ctor_get(v___x_3257_, 7);
v_snapshotTasks_3265_ = lean_ctor_get(v___x_3257_, 8);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; 
v_unused_3291_ = lean_ctor_get(v___x_3257_, 5);
lean_dec(v_unused_3291_);
v___x_3267_ = v___x_3257_;
v_isShared_3268_ = v_isSharedCheck_3290_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_snapshotTasks_3265_);
lean_inc(v_infoState_3264_);
lean_inc(v_messages_3263_);
lean_inc(v_traceState_3262_);
lean_inc(v_auxDeclNGen_3261_);
lean_inc(v_ngen_3260_);
lean_inc(v_nextMacroScope_3259_);
lean_inc(v_env_3258_);
lean_dec(v___x_3257_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3290_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
lean_inc(v_a_3250_);
v___x_3269_ = l_Lean_markMeta(v_env_3258_, v_a_3250_);
v___x_3270_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__2);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 5, v___x_3270_);
lean_ctor_set(v___x_3267_, 0, v___x_3269_);
v___x_3272_ = v___x_3267_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_nextMacroScope_3259_);
lean_ctor_set(v_reuseFailAlloc_3289_, 2, v_ngen_3260_);
lean_ctor_set(v_reuseFailAlloc_3289_, 3, v_auxDeclNGen_3261_);
lean_ctor_set(v_reuseFailAlloc_3289_, 4, v_traceState_3262_);
lean_ctor_set(v_reuseFailAlloc_3289_, 5, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3289_, 6, v_messages_3263_);
lean_ctor_set(v_reuseFailAlloc_3289_, 7, v_infoState_3264_);
lean_ctor_set(v_reuseFailAlloc_3289_, 8, v_snapshotTasks_3265_);
v___x_3272_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v_mctx_3275_; lean_object* v_zetaDeltaFVarIds_3276_; lean_object* v_postponed_3277_; lean_object* v_diag_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3287_; 
v___x_3273_ = lean_st_ref_set(v___y_3235_, v___x_3272_);
v___x_3274_ = lean_st_ref_take(v___y_3233_);
v_mctx_3275_ = lean_ctor_get(v___x_3274_, 0);
v_zetaDeltaFVarIds_3276_ = lean_ctor_get(v___x_3274_, 2);
v_postponed_3277_ = lean_ctor_get(v___x_3274_, 3);
v_diag_3278_ = lean_ctor_get(v___x_3274_, 4);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; 
v_unused_3288_ = lean_ctor_get(v___x_3274_, 1);
lean_dec(v_unused_3288_);
v___x_3280_ = v___x_3274_;
v_isShared_3281_ = v_isSharedCheck_3287_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_diag_3278_);
lean_inc(v_postponed_3277_);
lean_inc(v_zetaDeltaFVarIds_3276_);
lean_inc(v_mctx_3275_);
lean_dec(v___x_3274_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3287_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3282_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_normalizeInstance_spec__2___redArg___closed__3);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 1, v___x_3282_);
v___x_3284_ = v___x_3280_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_mctx_3275_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_zetaDeltaFVarIds_3276_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v_postponed_3277_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v_diag_3278_);
v___x_3284_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_st_ref_set(v___y_3233_, v___x_3284_);
v___y_3215_ = v_a_3250_;
v___y_3216_ = v_a_3254_;
v___y_3217_ = v___y_3234_;
v___y_3218_ = v___y_3235_;
goto v___jp_3214_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3250_);
return v___x_3253_;
}
}
else
{
lean_object* v___x_3293_; 
lean_dec(v_a_3243_);
lean_dec_ref(v_expectedType_3179_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v_a_3178_);
v___x_3293_ = v___x_3245_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3178_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec_ref(v_expectedType_3179_);
lean_dec_ref(v_a_3178_);
v_a_3296_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3242_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3242_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3179_);
lean_dec_ref(v_a_3178_);
return v___x_3240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__2(lean_object* v_expectedType_3459_, lean_object* v_inst_3460_, uint8_t v___x_3461_, uint8_t v_compile_3462_, uint8_t v_logCompileErrors_3463_, uint8_t v_isMeta_3464_, lean_object* v_____r_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; 
lean_inc_ref(v_expectedType_3459_);
v___x_3471_ = l_Lean_Meta_isProp(v_expectedType_3459_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3493_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3493_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3493_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_unbox(v_a_3472_);
lean_dec(v_a_3472_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; 
lean_del_object(v___x_3474_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc(v___y_3467_);
lean_inc_ref(v___y_3466_);
v___x_3477_ = lean_whnf(v_inst_3460_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v_dummy_3479_; lean_object* v_nargs_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v_dummy_3479_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_3480_ = l_Lean_Expr_getAppNumArgs(v_a_3478_);
lean_inc(v_nargs_3480_);
v___x_3481_ = lean_mk_array(v_nargs_3480_, v_dummy_3479_);
v___x_3482_ = lean_unsigned_to_nat(1u);
v___x_3483_ = lean_nat_sub(v_nargs_3480_, v___x_3482_);
lean_dec(v_nargs_3480_);
lean_inc(v_a_3478_);
v___x_3484_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15(v_a_3478_, v_expectedType_3459_, v___x_3461_, v_compile_3462_, v_logCompileErrors_3463_, v_isMeta_3464_, v_a_3478_, v___x_3481_, v___x_3483_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3484_;
}
else
{
lean_dec_ref(v_expectedType_3459_);
return v___x_3477_;
}
}
else
{
lean_object* v_options_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v_options_3485_ = lean_ctor_get(v___y_3468_, 2);
v___x_3486_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3487_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3485_, v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3489_; 
lean_dec_ref(v_expectedType_3459_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v_inst_3460_);
v___x_3489_ = v___x_3474_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_inst_3460_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_del_object(v___x_3474_);
v___x_3491_ = lean_box(0);
v___x_3492_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_3459_, v_inst_3460_, v___x_3461_, v___x_3491_, v___x_3461_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v_inst_3460_);
lean_dec_ref(v_expectedType_3459_);
v_a_3494_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3471_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3471_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance(lean_object* v_inst_3502_, lean_object* v_expectedType_3503_, uint8_t v_compile_3504_, uint8_t v_logCompileErrors_3505_, uint8_t v_isMeta_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v___x_3512_; lean_object* v_options_3513_; uint8_t v_foApprox_3514_; uint8_t v_ctxApprox_3515_; uint8_t v_quasiPatternApprox_3516_; uint8_t v_constApprox_3517_; uint8_t v_isDefEqStuckEx_3518_; uint8_t v_unificationHints_3519_; uint8_t v_proofIrrelevance_3520_; uint8_t v_assignSyntheticOpaque_3521_; uint8_t v_offsetCnstrs_3522_; uint8_t v_etaStruct_3523_; uint8_t v_univApprox_3524_; uint8_t v_iota_3525_; uint8_t v_beta_3526_; uint8_t v_proj_3527_; uint8_t v_zeta_3528_; uint8_t v_zetaDelta_3529_; uint8_t v_zetaUnused_3530_; uint8_t v_zetaHave_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3838_; 
v___x_3512_ = l_Lean_Meta_Context_config(v_a_3507_);
v_options_3513_ = lean_ctor_get(v_a_3509_, 2);
v_foApprox_3514_ = lean_ctor_get_uint8(v___x_3512_, 0);
v_ctxApprox_3515_ = lean_ctor_get_uint8(v___x_3512_, 1);
v_quasiPatternApprox_3516_ = lean_ctor_get_uint8(v___x_3512_, 2);
v_constApprox_3517_ = lean_ctor_get_uint8(v___x_3512_, 3);
v_isDefEqStuckEx_3518_ = lean_ctor_get_uint8(v___x_3512_, 4);
v_unificationHints_3519_ = lean_ctor_get_uint8(v___x_3512_, 5);
v_proofIrrelevance_3520_ = lean_ctor_get_uint8(v___x_3512_, 6);
v_assignSyntheticOpaque_3521_ = lean_ctor_get_uint8(v___x_3512_, 7);
v_offsetCnstrs_3522_ = lean_ctor_get_uint8(v___x_3512_, 8);
v_etaStruct_3523_ = lean_ctor_get_uint8(v___x_3512_, 10);
v_univApprox_3524_ = lean_ctor_get_uint8(v___x_3512_, 11);
v_iota_3525_ = lean_ctor_get_uint8(v___x_3512_, 12);
v_beta_3526_ = lean_ctor_get_uint8(v___x_3512_, 13);
v_proj_3527_ = lean_ctor_get_uint8(v___x_3512_, 14);
v_zeta_3528_ = lean_ctor_get_uint8(v___x_3512_, 15);
v_zetaDelta_3529_ = lean_ctor_get_uint8(v___x_3512_, 16);
v_zetaUnused_3530_ = lean_ctor_get_uint8(v___x_3512_, 17);
v_zetaHave_3531_ = lean_ctor_get_uint8(v___x_3512_, 18);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3533_ = v___x_3512_;
v_isShared_3534_ = v_isSharedCheck_3838_;
goto v_resetjp_3532_;
}
else
{
lean_dec(v___x_3512_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3838_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
uint8_t v_trackZetaDelta_3535_; lean_object* v_zetaDeltaSet_3536_; lean_object* v_lctx_3537_; lean_object* v_localInstances_3538_; lean_object* v_defEqCtx_x3f_3539_; lean_object* v_synthPendingDepth_3540_; lean_object* v_canUnfold_x3f_3541_; uint8_t v_univApprox_3542_; uint8_t v_inTypeClassResolution_3543_; uint8_t v_cacheInferType_3544_; uint8_t v_hasTrace_3545_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; uint8_t v___x_3582_; lean_object* v_config_3584_; 
v_trackZetaDelta_3535_ = lean_ctor_get_uint8(v_a_3507_, sizeof(void*)*7);
v_zetaDeltaSet_3536_ = lean_ctor_get(v_a_3507_, 1);
v_lctx_3537_ = lean_ctor_get(v_a_3507_, 2);
v_localInstances_3538_ = lean_ctor_get(v_a_3507_, 3);
v_defEqCtx_x3f_3539_ = lean_ctor_get(v_a_3507_, 4);
v_synthPendingDepth_3540_ = lean_ctor_get(v_a_3507_, 5);
v_canUnfold_x3f_3541_ = lean_ctor_get(v_a_3507_, 6);
v_univApprox_3542_ = lean_ctor_get_uint8(v_a_3507_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3543_ = lean_ctor_get_uint8(v_a_3507_, sizeof(void*)*7 + 2);
v_cacheInferType_3544_ = lean_ctor_get_uint8(v_a_3507_, sizeof(void*)*7 + 3);
v_hasTrace_3545_ = lean_ctor_get_uint8(v_options_3513_, sizeof(void*)*1);
v___x_3582_ = 3;
if (v_isShared_3534_ == 0)
{
v_config_3584_ = v___x_3533_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 0, v_foApprox_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 1, v_ctxApprox_3515_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 2, v_quasiPatternApprox_3516_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 3, v_constApprox_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 4, v_isDefEqStuckEx_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 5, v_unificationHints_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 6, v_proofIrrelevance_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 7, v_assignSyntheticOpaque_3521_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 8, v_offsetCnstrs_3522_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 10, v_etaStruct_3523_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 11, v_univApprox_3524_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 12, v_iota_3525_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 13, v_beta_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 14, v_proj_3527_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 15, v_zeta_3528_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 16, v_zetaDelta_3529_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 17, v_zetaUnused_3530_);
lean_ctor_set_uint8(v_reuseFailAlloc_3837_, 18, v_zetaHave_3531_);
v_config_3584_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3583_;
}
v___jp_3546_:
{
lean_object* v___x_3551_; 
lean_inc_ref(v_expectedType_3503_);
v___x_3551_ = l_Lean_Meta_isProp(v_expectedType_3503_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3573_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3573_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3573_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
uint8_t v___x_3556_; 
v___x_3556_ = lean_unbox(v_a_3552_);
lean_dec(v_a_3552_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
lean_del_object(v___x_3554_);
lean_inc(v___y_3550_);
lean_inc_ref(v___y_3549_);
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
v___x_3557_ = lean_whnf(v_inst_3502_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v_dummy_3559_; lean_object* v_nargs_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v___x_3557_);
v_dummy_3559_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_3560_ = l_Lean_Expr_getAppNumArgs(v_a_3558_);
lean_inc(v_nargs_3560_);
v___x_3561_ = lean_mk_array(v_nargs_3560_, v_dummy_3559_);
v___x_3562_ = lean_unsigned_to_nat(1u);
v___x_3563_ = lean_nat_sub(v_nargs_3560_, v___x_3562_);
lean_dec(v_nargs_3560_);
lean_inc(v_a_3558_);
v___x_3564_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10(v_a_3558_, v_expectedType_3503_, v_hasTrace_3545_, v_compile_3504_, v_logCompileErrors_3505_, v_isMeta_3506_, v_a_3558_, v___x_3561_, v___x_3563_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec_ref(v___y_3547_);
return v___x_3564_;
}
else
{
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_expectedType_3503_);
return v___x_3557_;
}
}
else
{
lean_object* v_options_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; 
v_options_3565_ = lean_ctor_get(v___y_3549_, 2);
v___x_3566_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3567_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3565_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3569_; 
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_expectedType_3503_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_inst_3502_);
v___x_3569_ = v___x_3554_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_inst_3502_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_del_object(v___x_3554_);
v___x_3571_ = lean_box(0);
v___x_3572_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_3503_, v_inst_3502_, v___x_3567_, v___x_3571_, v___x_3567_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec_ref(v___y_3547_);
return v___x_3572_;
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3574_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3551_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3551_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
v_reusejp_3583_:
{
uint64_t v___x_3585_; uint64_t v___x_3586_; uint64_t v___x_3587_; lean_object* v_cls_3588_; uint64_t v___x_3589_; uint64_t v___x_3590_; uint64_t v_key_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_ctor_set_uint8(v_config_3584_, 9, v___x_3582_);
v___x_3585_ = l_Lean_Meta_Context_configKey(v_a_3507_);
v___x_3586_ = 2ULL;
v___x_3587_ = lean_uint64_shift_right(v___x_3585_, v___x_3586_);
v_cls_3588_ = ((lean_object*)(l___private_Lean_Meta_InstanceNormalForm_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_InstanceNormalForm_2034682956____hygCtx___hyg_2_));
v___x_3589_ = lean_uint64_shift_left(v___x_3587_, v___x_3586_);
v___x_3590_ = lean_uint64_once(&l_Lean_Meta_normalizeInstance___closed__0, &l_Lean_Meta_normalizeInstance___closed__0_once, _init_l_Lean_Meta_normalizeInstance___closed__0);
v_key_3591_ = lean_uint64_lor(v___x_3589_, v___x_3590_);
v___x_3592_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3592_, 0, v_config_3584_);
lean_ctor_set_uint64(v___x_3592_, sizeof(void*)*1, v_key_3591_);
lean_inc(v_canUnfold_x3f_3541_);
lean_inc(v_synthPendingDepth_3540_);
lean_inc(v_defEqCtx_x3f_3539_);
lean_inc_ref(v_localInstances_3538_);
lean_inc_ref(v_lctx_3537_);
lean_inc(v_zetaDeltaSet_3536_);
v___x_3593_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v_zetaDeltaSet_3536_);
lean_ctor_set(v___x_3593_, 2, v_lctx_3537_);
lean_ctor_set(v___x_3593_, 3, v_localInstances_3538_);
lean_ctor_set(v___x_3593_, 4, v_defEqCtx_x3f_3539_);
lean_ctor_set(v___x_3593_, 5, v_synthPendingDepth_3540_);
lean_ctor_set(v___x_3593_, 6, v_canUnfold_x3f_3541_);
lean_ctor_set_uint8(v___x_3593_, sizeof(void*)*7, v_trackZetaDelta_3535_);
lean_ctor_set_uint8(v___x_3593_, sizeof(void*)*7 + 1, v_univApprox_3542_);
lean_ctor_set_uint8(v___x_3593_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3543_);
lean_ctor_set_uint8(v___x_3593_, sizeof(void*)*7 + 3, v_cacheInferType_3544_);
if (v_hasTrace_3545_ == 0)
{
lean_object* v___x_3594_; 
lean_inc_ref(v_expectedType_3503_);
v___x_3594_ = l_Lean_Meta_isClass_x3f(v_expectedType_3503_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3626_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3626_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3626_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
if (lean_obj_tag(v_a_3595_) == 1)
{
lean_object* v_val_3599_; lean_object* v___x_3600_; 
lean_del_object(v___x_3597_);
v_val_3599_ = lean_ctor_get(v_a_3595_, 0);
lean_inc(v_val_3599_);
lean_dec_ref(v_a_3595_);
v___x_3600_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3588_, v_a_3509_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; uint8_t v___x_3602_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref(v___x_3600_);
v___x_3602_ = lean_unbox(v_a_3601_);
lean_dec(v_a_3601_);
if (v___x_3602_ == 0)
{
lean_dec(v_val_3599_);
v___y_3547_ = v___x_3593_;
v___y_3548_ = v_a_3508_;
v___y_3549_ = v_a_3509_;
v___y_3550_ = v_a_3510_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3603_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___closed__2, &l_Lean_Meta_normalizeInstance___closed__2_once, _init_l_Lean_Meta_normalizeInstance___closed__2);
v___x_3604_ = l_Lean_MessageData_ofName(v_val_3599_);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3588_, v___x_3605_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_dec_ref(v___x_3606_);
v___y_3547_ = v___x_3593_;
v___y_3548_ = v_a_3508_;
v___y_3549_ = v_a_3509_;
v___y_3550_ = v_a_3510_;
goto v___jp_3546_;
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_val_3599_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3615_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3600_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3600_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v___x_3624_; 
lean_dec(v_a_3595_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v_inst_3502_);
v___x_3624_ = v___x_3597_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_inst_3502_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3627_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3594_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3594_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3588_, v_a_3509_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___f_3637_; lean_object* v___x_3638_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v_a_3642_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v_a_3655_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v_a_3660_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v_a_3671_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v_a_3687_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v_a_3692_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; uint8_t v___x_3749_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
lean_dec_ref(v___x_3635_);
lean_inc_ref(v_expectedType_3503_);
v___f_3637_ = lean_alloc_closure((void*)(l_Lean_Meta_normalizeInstance___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3637_, 0, v_expectedType_3503_);
v___x_3638_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4___closed__1));
v___x_3749_ = lean_unbox(v_a_3636_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; uint8_t v___x_3751_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; 
v___x_3750_ = l_Lean_trace_profiler;
v___x_3751_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3513_, v___x_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3788_; 
lean_dec_ref(v___f_3637_);
lean_dec(v_a_3636_);
lean_inc_ref(v_expectedType_3503_);
v___x_3788_ = l_Lean_Meta_isClass_x3f(v_expectedType_3503_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3820_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3820_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3820_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
if (lean_obj_tag(v_a_3789_) == 1)
{
lean_object* v_val_3793_; lean_object* v___x_3794_; 
lean_del_object(v___x_3791_);
v_val_3793_ = lean_ctor_get(v_a_3789_, 0);
lean_inc(v_val_3793_);
lean_dec_ref(v_a_3789_);
v___x_3794_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3588_, v_a_3509_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; uint8_t v___x_3796_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3794_);
v___x_3796_ = lean_unbox(v_a_3795_);
lean_dec(v_a_3795_);
if (v___x_3796_ == 0)
{
lean_dec(v_val_3793_);
v___y_3753_ = v___x_3593_;
v___y_3754_ = v_a_3508_;
v___y_3755_ = v_a_3509_;
v___y_3756_ = v_a_3510_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3797_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___closed__2, &l_Lean_Meta_normalizeInstance___closed__2_once, _init_l_Lean_Meta_normalizeInstance___closed__2);
v___x_3798_ = l_Lean_MessageData_ofName(v_val_3793_);
v___x_3799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3797_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3588_, v___x_3799_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_dec_ref(v___x_3800_);
v___y_3753_ = v___x_3593_;
v___y_3754_ = v_a_3508_;
v___y_3755_ = v_a_3509_;
v___y_3756_ = v_a_3510_;
goto v___jp_3752_;
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3800_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3800_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_val_3793_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3809_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3794_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3794_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
lean_object* v___x_3818_; 
lean_dec(v_a_3789_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v_inst_3502_);
v___x_3818_ = v___x_3791_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_inst_3502_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3821_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3788_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3788_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
goto v___jp_3700_;
}
v___jp_3752_:
{
lean_object* v___x_3757_; 
lean_inc_ref(v_expectedType_3503_);
v___x_3757_ = l_Lean_Meta_isProp(v_expectedType_3503_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3779_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3760_ = v___x_3757_;
v_isShared_3761_ = v_isSharedCheck_3779_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3757_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3779_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
uint8_t v___x_3762_; 
v___x_3762_ = lean_unbox(v_a_3758_);
lean_dec(v_a_3758_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
lean_del_object(v___x_3760_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
v___x_3763_ = lean_whnf(v_inst_3502_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v_dummy_3765_; lean_object* v_nargs_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref(v___x_3763_);
v_dummy_3765_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_3766_ = l_Lean_Expr_getAppNumArgs(v_a_3764_);
lean_inc(v_nargs_3766_);
v___x_3767_ = lean_mk_array(v_nargs_3766_, v_dummy_3765_);
v___x_3768_ = lean_unsigned_to_nat(1u);
v___x_3769_ = lean_nat_sub(v_nargs_3766_, v___x_3768_);
lean_dec(v_nargs_3766_);
lean_inc(v_a_3764_);
v___x_3770_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(v_a_3764_, v_expectedType_3503_, v___x_3751_, v_hasTrace_3545_, v_compile_3504_, v_logCompileErrors_3505_, v_isMeta_3506_, v_a_3764_, v___x_3767_, v___x_3769_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec_ref(v___y_3753_);
return v___x_3770_;
}
else
{
lean_dec_ref(v___y_3753_);
lean_dec_ref(v_expectedType_3503_);
return v___x_3763_;
}
}
else
{
lean_object* v_options_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v_options_3771_ = lean_ctor_get(v___y_3755_, 2);
v___x_3772_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3773_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3771_, v___x_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3775_; 
lean_dec_ref(v___y_3753_);
lean_dec_ref(v_expectedType_3503_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v_inst_3502_);
v___x_3775_ = v___x_3760_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_inst_3502_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_del_object(v___x_3760_);
v___x_3777_ = lean_box(0);
v___x_3778_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_3503_, v_inst_3502_, v_hasTrace_3545_, v___x_3777_, v_hasTrace_3545_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec_ref(v___y_3753_);
return v___x_3778_;
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec_ref(v___y_3753_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3780_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3757_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3757_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
}
else
{
goto v___jp_3700_;
}
v___jp_3639_:
{
lean_object* v___x_3643_; double v___x_3644_; double v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; lean_object* v___x_3651_; 
v___x_3643_ = lean_io_get_num_heartbeats();
v___x_3644_ = lean_float_of_nat(v___y_3641_);
v___x_3645_ = lean_float_of_nat(v___x_3643_);
v___x_3646_ = lean_box_float(v___x_3644_);
v___x_3647_ = lean_box_float(v___x_3645_);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v_a_3642_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_unbox(v_a_3636_);
lean_dec(v_a_3636_);
v___x_3651_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(v_cls_3588_, v_hasTrace_3545_, v___x_3638_, v_options_3513_, v___x_3650_, v___y_3640_, v___f_3637_, v___x_3649_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
lean_dec_ref(v___x_3593_);
return v___x_3651_;
}
v___jp_3652_:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_a_3655_);
v___y_3640_ = v___y_3653_;
v___y_3641_ = v___y_3654_;
v_a_3642_ = v___x_3656_;
goto v___jp_3639_;
}
v___jp_3657_:
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_a_3660_);
v___y_3640_ = v___y_3658_;
v___y_3641_ = v___y_3659_;
v_a_3642_ = v___x_3661_;
goto v___jp_3639_;
}
v___jp_3662_:
{
if (lean_obj_tag(v___y_3665_) == 0)
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v___y_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref(v___y_3665_);
v___y_3653_ = v___y_3663_;
v___y_3654_ = v___y_3664_;
v_a_3655_ = v_a_3666_;
goto v___jp_3652_;
}
else
{
lean_object* v_a_3667_; 
v_a_3667_ = lean_ctor_get(v___y_3665_, 0);
lean_inc(v_a_3667_);
lean_dec_ref(v___y_3665_);
v___y_3658_ = v___y_3663_;
v___y_3659_ = v___y_3664_;
v_a_3660_ = v_a_3667_;
goto v___jp_3657_;
}
}
v___jp_3668_:
{
lean_object* v___x_3672_; double v___x_3673_; double v___x_3674_; double v___x_3675_; double v___x_3676_; double v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; lean_object* v___x_3683_; 
v___x_3672_ = lean_io_mono_nanos_now();
v___x_3673_ = lean_float_of_nat(v___y_3669_);
v___x_3674_ = lean_float_once(&l_Lean_Meta_normalizeInstance___closed__3, &l_Lean_Meta_normalizeInstance___closed__3_once, _init_l_Lean_Meta_normalizeInstance___closed__3);
v___x_3675_ = lean_float_div(v___x_3673_, v___x_3674_);
v___x_3676_ = lean_float_of_nat(v___x_3672_);
v___x_3677_ = lean_float_div(v___x_3676_, v___x_3674_);
v___x_3678_ = lean_box_float(v___x_3675_);
v___x_3679_ = lean_box_float(v___x_3677_);
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3681_, 0, v_a_3671_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = lean_unbox(v_a_3636_);
lean_dec(v_a_3636_);
v___x_3683_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16(v_cls_3588_, v_hasTrace_3545_, v___x_3638_, v_options_3513_, v___x_3682_, v___y_3670_, v___f_3637_, v___x_3681_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
lean_dec_ref(v___x_3593_);
return v___x_3683_;
}
v___jp_3684_:
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3688_, 0, v_a_3687_);
v___y_3669_ = v___y_3685_;
v___y_3670_ = v___y_3686_;
v_a_3671_ = v___x_3688_;
goto v___jp_3668_;
}
v___jp_3689_:
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v_a_3692_);
v___y_3669_ = v___y_3690_;
v___y_3670_ = v___y_3691_;
v_a_3671_ = v___x_3693_;
goto v___jp_3668_;
}
v___jp_3694_:
{
if (lean_obj_tag(v___y_3697_) == 0)
{
lean_object* v_a_3698_; 
v_a_3698_ = lean_ctor_get(v___y_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref(v___y_3697_);
v___y_3685_ = v___y_3695_;
v___y_3686_ = v___y_3696_;
v_a_3687_ = v_a_3698_;
goto v___jp_3684_;
}
else
{
lean_object* v_a_3699_; 
v_a_3699_ = lean_ctor_get(v___y_3697_, 0);
lean_inc(v_a_3699_);
lean_dec_ref(v___y_3697_);
v___y_3690_ = v___y_3695_;
v___y_3691_ = v___y_3696_;
v_a_3692_ = v_a_3699_;
goto v___jp_3689_;
}
}
v___jp_3700_:
{
lean_object* v___x_3701_; 
v___x_3701_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_normalizeInstance_spec__11___redArg(v_a_3510_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref(v___x_3701_);
v___x_3703_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3704_ = l_Lean_Option_get___at___00Lean_Meta_normalizeInstance_spec__0(v_options_3513_, v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = lean_io_mono_nanos_now();
lean_inc_ref(v_expectedType_3503_);
v___x_3706_ = l_Lean_Meta_isClass_x3f(v_expectedType_3503_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref(v___x_3706_);
if (lean_obj_tag(v_a_3707_) == 1)
{
lean_object* v_val_3708_; lean_object* v___x_3709_; 
v_val_3708_ = lean_ctor_get(v_a_3707_, 0);
lean_inc(v_val_3708_);
lean_dec_ref(v_a_3707_);
v___x_3709_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3588_, v_a_3509_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; uint8_t v___x_3711_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref(v___x_3709_);
v___x_3711_ = lean_unbox(v_a_3710_);
lean_dec(v_a_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec(v_val_3708_);
v___x_3712_ = lean_box(0);
v___x_3713_ = l_Lean_Meta_normalizeInstance___lam__1(v_expectedType_3503_, v_inst_3502_, v___x_3704_, v_hasTrace_3545_, v_compile_3504_, v_logCompileErrors_3505_, v_isMeta_3506_, v___x_3712_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
v___y_3695_ = v___x_3705_;
v___y_3696_ = v_a_3702_;
v___y_3697_ = v___x_3713_;
goto v___jp_3694_;
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3714_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___closed__2, &l_Lean_Meta_normalizeInstance___closed__2_once, _init_l_Lean_Meta_normalizeInstance___closed__2);
v___x_3715_ = l_Lean_MessageData_ofName(v_val_3708_);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3588_, v___x_3716_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v___x_3719_ = l_Lean_Meta_normalizeInstance___lam__1(v_expectedType_3503_, v_inst_3502_, v___x_3704_, v_hasTrace_3545_, v_compile_3504_, v_logCompileErrors_3505_, v_isMeta_3506_, v_a_3718_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
v___y_3695_ = v___x_3705_;
v___y_3696_ = v_a_3702_;
v___y_3697_ = v___x_3719_;
goto v___jp_3694_;
}
else
{
lean_object* v_a_3720_; 
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3720_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3717_);
v___y_3690_ = v___x_3705_;
v___y_3691_ = v_a_3702_;
v_a_3692_ = v_a_3720_;
goto v___jp_3689_;
}
}
}
else
{
lean_object* v_a_3721_; 
lean_dec(v_val_3708_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3721_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3721_);
lean_dec_ref(v___x_3709_);
v___y_3690_ = v___x_3705_;
v___y_3691_ = v_a_3702_;
v_a_3692_ = v_a_3721_;
goto v___jp_3689_;
}
}
else
{
lean_dec(v_a_3707_);
lean_dec_ref(v_expectedType_3503_);
v___y_3685_ = v___x_3705_;
v___y_3686_ = v_a_3702_;
v_a_3687_ = v_inst_3502_;
goto v___jp_3684_;
}
}
else
{
lean_object* v_a_3722_; 
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3722_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3722_);
lean_dec_ref(v___x_3706_);
v___y_3690_ = v___x_3705_;
v___y_3691_ = v_a_3702_;
v_a_3692_ = v_a_3722_;
goto v___jp_3689_;
}
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_expectedType_3503_);
v___x_3724_ = l_Lean_Meta_isClass_x3f(v_expectedType_3503_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
if (lean_obj_tag(v_a_3725_) == 1)
{
lean_object* v_val_3726_; lean_object* v___x_3727_; 
v_val_3726_ = lean_ctor_get(v_a_3725_, 0);
lean_inc(v_val_3726_);
lean_dec_ref(v_a_3725_);
v___x_3727_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_normalizeInstance_spec__3___redArg(v_cls_3588_, v_a_3509_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; uint8_t v___x_3729_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = lean_unbox(v_a_3728_);
lean_dec(v_a_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
lean_dec(v_val_3726_);
v___x_3730_ = lean_box(0);
v___x_3731_ = l_Lean_Meta_normalizeInstance___lam__2(v_expectedType_3503_, v_inst_3502_, v___x_3704_, v_compile_3504_, v_logCompileErrors_3505_, v_isMeta_3506_, v___x_3730_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
v___y_3663_ = v_a_3702_;
v___y_3664_ = v___x_3723_;
v___y_3665_ = v___x_3731_;
goto v___jp_3662_;
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3732_ = lean_obj_once(&l_Lean_Meta_normalizeInstance___closed__2, &l_Lean_Meta_normalizeInstance___closed__2_once, _init_l_Lean_Meta_normalizeInstance___closed__2);
v___x_3733_ = l_Lean_MessageData_ofName(v_val_3726_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = l_Lean_addTrace___at___00Lean_Meta_normalizeInstance_spec__4(v_cls_3588_, v___x_3734_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref(v___x_3735_);
v___x_3737_ = l_Lean_Meta_normalizeInstance___lam__2(v_expectedType_3503_, v_inst_3502_, v___x_3704_, v_compile_3504_, v_logCompileErrors_3505_, v_isMeta_3506_, v_a_3736_, v___x_3593_, v_a_3508_, v_a_3509_, v_a_3510_);
v___y_3663_ = v_a_3702_;
v___y_3664_ = v___x_3723_;
v___y_3665_ = v___x_3737_;
goto v___jp_3662_;
}
else
{
lean_object* v_a_3738_; 
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3738_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___x_3735_);
v___y_3658_ = v_a_3702_;
v___y_3659_ = v___x_3723_;
v_a_3660_ = v_a_3738_;
goto v___jp_3657_;
}
}
}
else
{
lean_object* v_a_3739_; 
lean_dec(v_val_3726_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3739_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3739_);
lean_dec_ref(v___x_3727_);
v___y_3658_ = v_a_3702_;
v___y_3659_ = v___x_3723_;
v_a_3660_ = v_a_3739_;
goto v___jp_3657_;
}
}
else
{
lean_dec(v_a_3725_);
lean_dec_ref(v_expectedType_3503_);
v___y_3653_ = v_a_3702_;
v___y_3654_ = v___x_3723_;
v_a_3655_ = v_inst_3502_;
goto v___jp_3652_;
}
}
else
{
lean_object* v_a_3740_; 
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3740_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3740_);
lean_dec_ref(v___x_3724_);
v___y_3658_ = v_a_3702_;
v___y_3659_ = v___x_3723_;
v_a_3660_ = v_a_3740_;
goto v___jp_3657_;
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v___f_3637_);
lean_dec(v_a_3636_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3741_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3701_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3701_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref(v___x_3593_);
lean_dec_ref(v_expectedType_3503_);
lean_dec_ref(v_inst_3502_);
v_a_3829_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3635_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3635_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(lean_object* v___x_3839_, lean_object* v_a_3840_, uint8_t v_compile_3841_, uint8_t v_logCompileErrors_3842_, uint8_t v_isMeta_3843_, lean_object* v___x_3844_, lean_object* v___x_3845_, lean_object* v_____r_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Lean_Meta_normalizeInstance(v___x_3839_, v_a_3840_, v_compile_3841_, v_logCompileErrors_3842_, v_isMeta_3843_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3844_, v_a_3853_, v___y_3848_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3862_; 
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; 
v_unused_3863_ = lean_ctor_get(v___x_3854_, 0);
lean_dec(v_unused_3863_);
v___x_3856_ = v___x_3854_;
v_isShared_3857_ = v_isSharedCheck_3862_;
goto v_resetjp_3855_;
}
else
{
lean_dec(v___x_3854_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3862_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3845_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v___x_3858_);
v___x_3860_ = v___x_3856_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
v_a_3864_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3854_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3854_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec(v___x_3844_);
v_a_3872_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3852_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3852_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1___boxed(lean_object* v___x_3880_, lean_object* v_a_3881_, lean_object* v_compile_3882_, lean_object* v_logCompileErrors_3883_, lean_object* v_isMeta_3884_, lean_object* v___x_3885_, lean_object* v___x_3886_, lean_object* v_____r_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v_compile_boxed_3893_; uint8_t v_logCompileErrors_boxed_3894_; uint8_t v_isMeta_boxed_3895_; lean_object* v_res_3896_; 
v_compile_boxed_3893_ = lean_unbox(v_compile_3882_);
v_logCompileErrors_boxed_3894_ = lean_unbox(v_logCompileErrors_3883_);
v_isMeta_boxed_3895_ = lean_unbox(v_isMeta_3884_);
v_res_3896_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___lam__1(v___x_3880_, v_a_3881_, v_compile_boxed_3893_, v_logCompileErrors_boxed_3894_, v_isMeta_boxed_3895_, v___x_3885_, v___x_3886_, v_____r_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__1___boxed(lean_object* v_expectedType_3897_, lean_object* v_inst_3898_, lean_object* v___x_3899_, lean_object* v_hasTrace_3900_, lean_object* v_compile_3901_, lean_object* v_logCompileErrors_3902_, lean_object* v_isMeta_3903_, lean_object* v_____r_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
uint8_t v___x_110114__boxed_3910_; uint8_t v_hasTrace_boxed_3911_; uint8_t v_compile_boxed_3912_; uint8_t v_logCompileErrors_boxed_3913_; uint8_t v_isMeta_boxed_3914_; lean_object* v_res_3915_; 
v___x_110114__boxed_3910_ = lean_unbox(v___x_3899_);
v_hasTrace_boxed_3911_ = lean_unbox(v_hasTrace_3900_);
v_compile_boxed_3912_ = lean_unbox(v_compile_3901_);
v_logCompileErrors_boxed_3913_ = lean_unbox(v_logCompileErrors_3902_);
v_isMeta_boxed_3914_ = lean_unbox(v_isMeta_3903_);
v_res_3915_ = l_Lean_Meta_normalizeInstance___lam__1(v_expectedType_3897_, v_inst_3898_, v___x_110114__boxed_3910_, v_hasTrace_boxed_3911_, v_compile_boxed_3912_, v_logCompileErrors_boxed_3913_, v_isMeta_boxed_3914_, v_____r_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___lam__2___boxed(lean_object* v_expectedType_3916_, lean_object* v_inst_3917_, lean_object* v___x_3918_, lean_object* v_compile_3919_, lean_object* v_logCompileErrors_3920_, lean_object* v_isMeta_3921_, lean_object* v_____r_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
uint8_t v___x_110138__boxed_3928_; uint8_t v_compile_boxed_3929_; uint8_t v_logCompileErrors_boxed_3930_; uint8_t v_isMeta_boxed_3931_; lean_object* v_res_3932_; 
v___x_110138__boxed_3928_ = lean_unbox(v___x_3918_);
v_compile_boxed_3929_ = lean_unbox(v_compile_3919_);
v_logCompileErrors_boxed_3930_ = lean_unbox(v_logCompileErrors_3920_);
v_isMeta_boxed_3931_ = lean_unbox(v_isMeta_3921_);
v_res_3932_ = l_Lean_Meta_normalizeInstance___lam__2(v_expectedType_3916_, v_inst_3917_, v___x_110138__boxed_3928_, v_compile_boxed_3929_, v_logCompileErrors_boxed_3930_, v_isMeta_boxed_3931_, v_____r_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13___boxed(lean_object* v_a_3933_, lean_object* v_expectedType_3934_, lean_object* v___x_3935_, lean_object* v___x_3936_, lean_object* v_compile_3937_, lean_object* v_logCompileErrors_3938_, lean_object* v_isMeta_3939_, lean_object* v_x_3940_, lean_object* v_x_3941_, lean_object* v_x_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
uint8_t v___x_110181__boxed_3948_; uint8_t v___x_110182__boxed_3949_; uint8_t v_compile_boxed_3950_; uint8_t v_logCompileErrors_boxed_3951_; uint8_t v_isMeta_boxed_3952_; lean_object* v_res_3953_; 
v___x_110181__boxed_3948_ = lean_unbox(v___x_3935_);
v___x_110182__boxed_3949_ = lean_unbox(v___x_3936_);
v_compile_boxed_3950_ = lean_unbox(v_compile_3937_);
v_logCompileErrors_boxed_3951_ = lean_unbox(v_logCompileErrors_3938_);
v_isMeta_boxed_3952_ = lean_unbox(v_isMeta_3939_);
v_res_3953_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__13(v_a_3933_, v_expectedType_3934_, v___x_110181__boxed_3948_, v___x_110182__boxed_3949_, v_compile_boxed_3950_, v_logCompileErrors_boxed_3951_, v_isMeta_boxed_3952_, v_x_3940_, v_x_3941_, v_x_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15___boxed(lean_object* v_a_3954_, lean_object* v_expectedType_3955_, lean_object* v___x_3956_, lean_object* v_compile_3957_, lean_object* v_logCompileErrors_3958_, lean_object* v_isMeta_3959_, lean_object* v_x_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
uint8_t v___x_110338__boxed_3968_; uint8_t v_compile_boxed_3969_; uint8_t v_logCompileErrors_boxed_3970_; uint8_t v_isMeta_boxed_3971_; lean_object* v_res_3972_; 
v___x_110338__boxed_3968_ = lean_unbox(v___x_3956_);
v_compile_boxed_3969_ = lean_unbox(v_compile_3957_);
v_logCompileErrors_boxed_3970_ = lean_unbox(v_logCompileErrors_3958_);
v_isMeta_boxed_3971_ = lean_unbox(v_isMeta_3959_);
v_res_3972_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__15(v_a_3954_, v_expectedType_3955_, v___x_110338__boxed_3968_, v_compile_boxed_3969_, v_logCompileErrors_boxed_3970_, v_isMeta_boxed_3971_, v_x_3960_, v_x_3961_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10___boxed(lean_object* v_a_3973_, lean_object* v_expectedType_3974_, lean_object* v___x_3975_, lean_object* v_compile_3976_, lean_object* v_logCompileErrors_3977_, lean_object* v_isMeta_3978_, lean_object* v_x_3979_, lean_object* v_x_3980_, lean_object* v_x_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v___x_110505__boxed_3987_; uint8_t v_compile_boxed_3988_; uint8_t v_logCompileErrors_boxed_3989_; uint8_t v_isMeta_boxed_3990_; lean_object* v_res_3991_; 
v___x_110505__boxed_3987_ = lean_unbox(v___x_3975_);
v_compile_boxed_3988_ = lean_unbox(v_compile_3976_);
v_logCompileErrors_boxed_3989_ = lean_unbox(v_logCompileErrors_3977_);
v_isMeta_boxed_3990_ = lean_unbox(v_isMeta_3978_);
v_res_3991_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_normalizeInstance_spec__10(v_a_3973_, v_expectedType_3974_, v___x_110505__boxed_3987_, v_compile_boxed_3988_, v_logCompileErrors_boxed_3989_, v_isMeta_boxed_3990_, v_x_3979_, v_x_3980_, v_x_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg___boxed(lean_object* v_upperBound_3992_, lean_object* v_fst_3993_, lean_object* v_args_3994_, lean_object* v_compile_3995_, lean_object* v_logCompileErrors_3996_, lean_object* v_isMeta_3997_, lean_object* v___x_3998_, lean_object* v_a_3999_, lean_object* v_b_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
uint8_t v_compile_boxed_4006_; uint8_t v_logCompileErrors_boxed_4007_; uint8_t v_isMeta_boxed_4008_; uint8_t v___x_110689__boxed_4009_; lean_object* v_res_4010_; 
v_compile_boxed_4006_ = lean_unbox(v_compile_3995_);
v_logCompileErrors_boxed_4007_ = lean_unbox(v_logCompileErrors_3996_);
v_isMeta_boxed_4008_ = lean_unbox(v_isMeta_3997_);
v___x_110689__boxed_4009_ = lean_unbox(v___x_3998_);
v_res_4010_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(v_upperBound_3992_, v_fst_3993_, v_args_3994_, v_compile_boxed_4006_, v_logCompileErrors_boxed_4007_, v_isMeta_boxed_4008_, v___x_110689__boxed_4009_, v_a_3999_, v_b_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec_ref(v_args_3994_);
lean_dec_ref(v_fst_3993_);
lean_dec(v_upperBound_3992_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg___boxed(lean_object* v_upperBound_4011_, lean_object* v_fst_4012_, lean_object* v_args_4013_, lean_object* v___x_4014_, lean_object* v_compile_4015_, lean_object* v_logCompileErrors_4016_, lean_object* v_isMeta_4017_, lean_object* v___x_4018_, lean_object* v_a_4019_, lean_object* v_b_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
uint8_t v___x_110845__boxed_4026_; uint8_t v_compile_boxed_4027_; uint8_t v_logCompileErrors_boxed_4028_; uint8_t v_isMeta_boxed_4029_; uint8_t v___x_110846__boxed_4030_; lean_object* v_res_4031_; 
v___x_110845__boxed_4026_ = lean_unbox(v___x_4014_);
v_compile_boxed_4027_ = lean_unbox(v_compile_4015_);
v_logCompileErrors_boxed_4028_ = lean_unbox(v_logCompileErrors_4016_);
v_isMeta_boxed_4029_ = lean_unbox(v_isMeta_4017_);
v___x_110846__boxed_4030_ = lean_unbox(v___x_4018_);
v_res_4031_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(v_upperBound_4011_, v_fst_4012_, v_args_4013_, v___x_110845__boxed_4026_, v_compile_boxed_4027_, v_logCompileErrors_boxed_4028_, v_isMeta_boxed_4029_, v___x_110846__boxed_4030_, v_a_4019_, v_b_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec_ref(v_args_4013_);
lean_dec_ref(v_fst_4012_);
lean_dec(v_upperBound_4011_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg___boxed(lean_object* v_upperBound_4032_, lean_object* v_fst_4033_, lean_object* v_args_4034_, lean_object* v___x_4035_, lean_object* v_compile_4036_, lean_object* v_logCompileErrors_4037_, lean_object* v_isMeta_4038_, lean_object* v_a_4039_, lean_object* v_b_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
uint8_t v___x_111014__boxed_4046_; uint8_t v_compile_boxed_4047_; uint8_t v_logCompileErrors_boxed_4048_; uint8_t v_isMeta_boxed_4049_; lean_object* v_res_4050_; 
v___x_111014__boxed_4046_ = lean_unbox(v___x_4035_);
v_compile_boxed_4047_ = lean_unbox(v_compile_4036_);
v_logCompileErrors_boxed_4048_ = lean_unbox(v_logCompileErrors_4037_);
v_isMeta_boxed_4049_ = lean_unbox(v_isMeta_4038_);
v_res_4050_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(v_upperBound_4032_, v_fst_4033_, v_args_4034_, v___x_111014__boxed_4046_, v_compile_boxed_4047_, v_logCompileErrors_boxed_4048_, v_isMeta_boxed_4049_, v_a_4039_, v_b_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec_ref(v_args_4034_);
lean_dec_ref(v_fst_4033_);
lean_dec(v_upperBound_4032_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_normalizeInstance___boxed(lean_object* v_inst_4051_, lean_object* v_expectedType_4052_, lean_object* v_compile_4053_, lean_object* v_logCompileErrors_4054_, lean_object* v_isMeta_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
uint8_t v_compile_boxed_4061_; uint8_t v_logCompileErrors_boxed_4062_; uint8_t v_isMeta_boxed_4063_; lean_object* v_res_4064_; 
v_compile_boxed_4061_ = lean_unbox(v_compile_4053_);
v_logCompileErrors_boxed_4062_ = lean_unbox(v_logCompileErrors_4054_);
v_isMeta_boxed_4063_ = lean_unbox(v_isMeta_4055_);
v_res_4064_ = l_Lean_Meta_normalizeInstance(v_inst_4051_, v_expectedType_4052_, v_compile_boxed_4061_, v_logCompileErrors_boxed_4062_, v_isMeta_boxed_4063_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6(size_t v_sz_4065_, size_t v_i_4066_, lean_object* v_bs_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___redArg(v_sz_4065_, v_i_4066_, v_bs_4067_, v___y_4069_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6___boxed(lean_object* v_sz_4074_, lean_object* v_i_4075_, lean_object* v_bs_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
size_t v_sz_boxed_4082_; size_t v_i_boxed_4083_; lean_object* v_res_4084_; 
v_sz_boxed_4082_ = lean_unbox_usize(v_sz_4074_);
lean_dec(v_sz_4074_);
v_i_boxed_4083_ = lean_unbox_usize(v_i_4075_);
lean_dec(v_i_4075_);
v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_normalizeInstance_spec__6(v_sz_boxed_4082_, v_i_boxed_4083_, v_bs_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7(lean_object* v_upperBound_4085_, lean_object* v_fst_4086_, lean_object* v_args_4087_, uint8_t v_compile_4088_, uint8_t v_logCompileErrors_4089_, uint8_t v_isMeta_4090_, uint8_t v___x_4091_, lean_object* v_inst_4092_, lean_object* v_R_4093_, lean_object* v_a_4094_, lean_object* v_b_4095_, lean_object* v_c_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___redArg(v_upperBound_4085_, v_fst_4086_, v_args_4087_, v_compile_4088_, v_logCompileErrors_4089_, v_isMeta_4090_, v___x_4091_, v_a_4094_, v_b_4095_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7___boxed(lean_object** _args){
lean_object* v_upperBound_4103_ = _args[0];
lean_object* v_fst_4104_ = _args[1];
lean_object* v_args_4105_ = _args[2];
lean_object* v_compile_4106_ = _args[3];
lean_object* v_logCompileErrors_4107_ = _args[4];
lean_object* v_isMeta_4108_ = _args[5];
lean_object* v___x_4109_ = _args[6];
lean_object* v_inst_4110_ = _args[7];
lean_object* v_R_4111_ = _args[8];
lean_object* v_a_4112_ = _args[9];
lean_object* v_b_4113_ = _args[10];
lean_object* v_c_4114_ = _args[11];
lean_object* v___y_4115_ = _args[12];
lean_object* v___y_4116_ = _args[13];
lean_object* v___y_4117_ = _args[14];
lean_object* v___y_4118_ = _args[15];
lean_object* v___y_4119_ = _args[16];
_start:
{
uint8_t v_compile_boxed_4120_; uint8_t v_logCompileErrors_boxed_4121_; uint8_t v_isMeta_boxed_4122_; uint8_t v___x_114244__boxed_4123_; lean_object* v_res_4124_; 
v_compile_boxed_4120_ = lean_unbox(v_compile_4106_);
v_logCompileErrors_boxed_4121_ = lean_unbox(v_logCompileErrors_4107_);
v_isMeta_boxed_4122_ = lean_unbox(v_isMeta_4108_);
v___x_114244__boxed_4123_ = lean_unbox(v___x_4109_);
v_res_4124_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__7(v_upperBound_4103_, v_fst_4104_, v_args_4105_, v_compile_boxed_4120_, v_logCompileErrors_boxed_4121_, v_isMeta_boxed_4122_, v___x_114244__boxed_4123_, v_inst_4110_, v_R_4111_, v_a_4112_, v_b_4113_, v_c_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec_ref(v_args_4105_);
lean_dec_ref(v_fst_4104_);
lean_dec(v_upperBound_4103_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8(lean_object* v_00_u03b1_4125_, lean_object* v_msg_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___redArg(v_msg_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8___boxed(lean_object* v_00_u03b1_4133_, lean_object* v_msg_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_throwError___at___00Lean_Meta_normalizeInstance_spec__8(v_00_u03b1_4133_, v_msg_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12(lean_object* v_upperBound_4141_, lean_object* v_fst_4142_, lean_object* v_args_4143_, uint8_t v___x_4144_, uint8_t v_compile_4145_, uint8_t v_logCompileErrors_4146_, uint8_t v_isMeta_4147_, uint8_t v___x_4148_, lean_object* v_inst_4149_, lean_object* v_R_4150_, lean_object* v_a_4151_, lean_object* v_b_4152_, lean_object* v_c_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___redArg(v_upperBound_4141_, v_fst_4142_, v_args_4143_, v___x_4144_, v_compile_4145_, v_logCompileErrors_4146_, v_isMeta_4147_, v___x_4148_, v_a_4151_, v_b_4152_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_4160_ = _args[0];
lean_object* v_fst_4161_ = _args[1];
lean_object* v_args_4162_ = _args[2];
lean_object* v___x_4163_ = _args[3];
lean_object* v_compile_4164_ = _args[4];
lean_object* v_logCompileErrors_4165_ = _args[5];
lean_object* v_isMeta_4166_ = _args[6];
lean_object* v___x_4167_ = _args[7];
lean_object* v_inst_4168_ = _args[8];
lean_object* v_R_4169_ = _args[9];
lean_object* v_a_4170_ = _args[10];
lean_object* v_b_4171_ = _args[11];
lean_object* v_c_4172_ = _args[12];
lean_object* v___y_4173_ = _args[13];
lean_object* v___y_4174_ = _args[14];
lean_object* v___y_4175_ = _args[15];
lean_object* v___y_4176_ = _args[16];
lean_object* v___y_4177_ = _args[17];
_start:
{
uint8_t v___x_114290__boxed_4178_; uint8_t v_compile_boxed_4179_; uint8_t v_logCompileErrors_boxed_4180_; uint8_t v_isMeta_boxed_4181_; uint8_t v___x_114291__boxed_4182_; lean_object* v_res_4183_; 
v___x_114290__boxed_4178_ = lean_unbox(v___x_4163_);
v_compile_boxed_4179_ = lean_unbox(v_compile_4164_);
v_logCompileErrors_boxed_4180_ = lean_unbox(v_logCompileErrors_4165_);
v_isMeta_boxed_4181_ = lean_unbox(v_isMeta_4166_);
v___x_114291__boxed_4182_ = lean_unbox(v___x_4167_);
v_res_4183_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__12(v_upperBound_4160_, v_fst_4161_, v_args_4162_, v___x_114290__boxed_4178_, v_compile_boxed_4179_, v_logCompileErrors_boxed_4180_, v_isMeta_boxed_4181_, v___x_114291__boxed_4182_, v_inst_4168_, v_R_4169_, v_a_4170_, v_b_4171_, v_c_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec_ref(v_args_4162_);
lean_dec_ref(v_fst_4161_);
lean_dec(v_upperBound_4160_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14(lean_object* v_upperBound_4184_, lean_object* v_fst_4185_, lean_object* v_args_4186_, uint8_t v___x_4187_, uint8_t v_compile_4188_, uint8_t v_logCompileErrors_4189_, uint8_t v_isMeta_4190_, lean_object* v_inst_4191_, lean_object* v_R_4192_, lean_object* v_a_4193_, lean_object* v_b_4194_, lean_object* v_c_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___redArg(v_upperBound_4184_, v_fst_4185_, v_args_4186_, v___x_4187_, v_compile_4188_, v_logCompileErrors_4189_, v_isMeta_4190_, v_a_4193_, v_b_4194_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14___boxed(lean_object** _args){
lean_object* v_upperBound_4202_ = _args[0];
lean_object* v_fst_4203_ = _args[1];
lean_object* v_args_4204_ = _args[2];
lean_object* v___x_4205_ = _args[3];
lean_object* v_compile_4206_ = _args[4];
lean_object* v_logCompileErrors_4207_ = _args[5];
lean_object* v_isMeta_4208_ = _args[6];
lean_object* v_inst_4209_ = _args[7];
lean_object* v_R_4210_ = _args[8];
lean_object* v_a_4211_ = _args[9];
lean_object* v_b_4212_ = _args[10];
lean_object* v_c_4213_ = _args[11];
lean_object* v___y_4214_ = _args[12];
lean_object* v___y_4215_ = _args[13];
lean_object* v___y_4216_ = _args[14];
lean_object* v___y_4217_ = _args[15];
lean_object* v___y_4218_ = _args[16];
_start:
{
uint8_t v___x_114322__boxed_4219_; uint8_t v_compile_boxed_4220_; uint8_t v_logCompileErrors_boxed_4221_; uint8_t v_isMeta_boxed_4222_; lean_object* v_res_4223_; 
v___x_114322__boxed_4219_ = lean_unbox(v___x_4205_);
v_compile_boxed_4220_ = lean_unbox(v_compile_4206_);
v_logCompileErrors_boxed_4221_ = lean_unbox(v_logCompileErrors_4207_);
v_isMeta_boxed_4222_ = lean_unbox(v_isMeta_4208_);
v_res_4223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_normalizeInstance_spec__14(v_upperBound_4202_, v_fst_4203_, v_args_4204_, v___x_114322__boxed_4219_, v_compile_boxed_4220_, v_logCompileErrors_boxed_4221_, v_isMeta_boxed_4222_, v_inst_4209_, v_R_4210_, v_a_4211_, v_b_4212_, v_c_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v_args_4204_);
lean_dec_ref(v_fst_4203_);
lean_dec(v_upperBound_4202_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20(lean_object* v_00_u03b1_4224_, lean_object* v_x_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___redArg(v_x_4225_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20___boxed(lean_object* v_00_u03b1_4232_, lean_object* v_x_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_normalizeInstance_spec__16_spec__20(v_00_u03b1_4232_, v_x_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6(lean_object* v_00_u03b1_4240_, lean_object* v_constName_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___redArg(v_constName_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4248_, lean_object* v_constName_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6(v_00_u03b1_4248_, v_constName_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_4256_, lean_object* v_ref_4257_, lean_object* v_constName_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___redArg(v_ref_4257_, v_constName_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_4265_, lean_object* v_ref_4266_, lean_object* v_constName_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8(v_00_u03b1_4265_, v_ref_4266_, v_constName_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v_ref_4266_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22(lean_object* v_00_u03b1_4274_, lean_object* v_ref_4275_, lean_object* v_msg_4276_, lean_object* v_declHint_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___redArg(v_ref_4275_, v_msg_4276_, v_declHint_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22___boxed(lean_object* v_00_u03b1_4284_, lean_object* v_ref_4285_, lean_object* v_msg_4286_, lean_object* v_declHint_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22(v_00_u03b1_4284_, v_ref_4285_, v_msg_4286_, v_declHint_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v_ref_4285_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26(lean_object* v_msg_4294_, lean_object* v_declHint_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___redArg(v_msg_4294_, v_declHint_4295_, v___y_4299_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26___boxed(lean_object* v_msg_4302_, lean_object* v_declHint_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__24_spec__26(v_msg_4302_, v_declHint_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25(lean_object* v_00_u03b1_4310_, lean_object* v_ref_4311_, lean_object* v_msg_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___redArg(v_ref_4311_, v_msg_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25___boxed(lean_object* v_00_u03b1_4319_, lean_object* v_ref_4320_, lean_object* v_msg_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_normalizeInstance_spec__5_spec__6_spec__8_spec__22_spec__25(v_00_u03b1_4319_, v_ref_4320_, v_msg_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v_ref_4320_);
return v_res_4327_;
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
