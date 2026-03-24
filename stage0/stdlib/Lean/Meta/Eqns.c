// Lean compiler output
// Module: Lean.Meta.Eqns
// Imports: public import Lean.Meta.Match.MatcherInfo public import Lean.DefEqAttrib public import Lean.Meta.RecExt public import Lean.Meta.LetToHave import Lean.Meta.AppBuilder
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_is_matcher(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_registerReservedNameAction(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eqns"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nonrecursive"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 23, 21, 28, 3, 196, 180, 100)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(1, 23, 146, 109, 99, 186, 103, 88)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "Create fine-grained equational lemmas even for non-recursive definitions."};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 217, 222, 73, 223, 67, 131, 25)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(156, 7, 83, 198, 209, 69, 31, 191)}};
static const lean_object* l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_eqns_nonrecursive;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "deepRecursiveSplit"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 23, 21, 28, 3, 196, 180, 100)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(167, 67, 13, 105, 163, 80, 199, 218)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 339, .m_capacity = 339, .m_length = 338, .m_data = "Create equational lemmas for recursive functions like for non-recursive functions. If disabled, match statements in recursive function definitions that do not contain recursive calls do not cause further splits in the equational lemmas. This was the behavior before Lean 4.12, and the purpose of this option is to help migrating old code."};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 217, 222, 73, 223, 67, 131, 25)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(226, 35, 35, 130, 249, 93, 79, 68)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_eqns_deepRecursiveSplit;
static lean_once_cell_t l_Lean_Meta_eqnAffectingOptions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_eqnAffectingOptions;
static const lean_string_object l_Lean_Meta_eqnThmSuffixBase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_Lean_Meta_eqnThmSuffixBase___closed__0 = (const lean_object*)&l_Lean_Meta_eqnThmSuffixBase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_eqnThmSuffixBase = (const lean_object*)&l_Lean_Meta_eqnThmSuffixBase___closed__0_value;
static const lean_string_object l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eq_"};
static const lean_object* l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0 = (const lean_object*)&l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_eqnThmSuffixBasePrefix = (const lean_object*)&l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0_value;
static const lean_string_object l_Lean_Meta_eqn1ThmSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eq_1"};
static const lean_object* l_Lean_Meta_eqn1ThmSuffix___closed__0 = (const lean_object*)&l_Lean_Meta_eqn1ThmSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_eqn1ThmSuffix = (const lean_object*)&l_Lean_Meta_eqn1ThmSuffix___closed__0_value;
static lean_once_cell_t l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isEqnReservedNameSuffix___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_unfoldThmSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "eq_def"};
static const lean_object* l_Lean_Meta_unfoldThmSuffix___closed__0 = (const lean_object*)&l_Lean_Meta_unfoldThmSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_unfoldThmSuffix = (const lean_object*)&l_Lean_Meta_unfoldThmSuffix___closed__0_value;
static const lean_string_object l_Lean_Meta_eqUnfoldThmSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_unfold"};
static const lean_object* l_Lean_Meta_eqUnfoldThmSuffix___closed__0 = (const lean_object*)&l_Lean_Meta_eqUnfoldThmSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_eqUnfoldThmSuffix = (const lean_object*)&l_Lean_Meta_eqUnfoldThmSuffix___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "failed to declare `"};
static const lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1;
static const lean_string_object l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` because `"};
static const lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3;
static const lean_string_object l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4_value;
static lean_once_cell_t l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
static const lean_string_object l_Lean_Meta_registerGetEqnsFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "failed to register equation getter, this kind of extension can only be registered during initialization"};
static const lean_object* l_Lean_Meta_registerGetEqnsFn___closed__0 = (const lean_object*)&l_Lean_Meta_registerGetEqnsFn___closed__0_value;
static lean_once_cell_t l_Lean_Meta_registerGetEqnsFn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerGetEqnsFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedEqnsExtState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedEqnsExtState;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqnsExt;
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2;
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_generateEagerEqns___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Meta_generateEagerEqns___closed__0;
static const lean_string_object l_Lean_Meta_generateEagerEqns___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Meta_generateEagerEqns___closed__1 = (const lean_object*)&l_Lean_Meta_generateEagerEqns___closed__1_value;
static const lean_string_object l_Lean_Meta_generateEagerEqns___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Meta_generateEagerEqns___closed__2 = (const lean_object*)&l_Lean_Meta_generateEagerEqns___closed__2_value;
static const lean_ctor_object l_Lean_Meta_generateEagerEqns___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_generateEagerEqns___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Meta_generateEagerEqns___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_generateEagerEqns___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_generateEagerEqns___closed__2_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Meta_generateEagerEqns___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_generateEagerEqns___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 70, 141, 178, 157, 107, 140, 91)}};
static const lean_object* l_Lean_Meta_generateEagerEqns___closed__3 = (const lean_object*)&l_Lean_Meta_generateEagerEqns___closed__3_value;
static const lean_string_object l_Lean_Meta_generateEagerEqns___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "generating eager equations for "};
static const lean_object* l_Lean_Meta_generateEagerEqns___closed__4 = (const lean_object*)&l_Lean_Meta_generateEagerEqns___closed__4_value;
static lean_once_cell_t l_Lean_Meta_generateEagerEqns___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_generateEagerEqns___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "invalid unfold theorem name `"};
static const lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` has been generated expected `"};
static const lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Eqns reserved name action for "};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ReservedNameAction"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 245, 189, 90, 36, 141, 82, 229)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Eqns"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 217, 145, 26, 133, 108, 104, 10)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(27, 2, 5, 79, 97, 142, 74, 217)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 112, 146, 108, 241, 250, 100, 162)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 0, 196, 176, 89, 93, 16, 10)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 31, 160, 103, 40, 58, 110, 116)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 147, 153, 14, 107, 3, 39, 172)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 114, 185, 94, 205, 199, 191, 156)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 255, 177, 29, 188, 255, 188, 249)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 48, 196, 25, 136, 122, 168, 47)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_));
v___x_62_ = ((lean_object*)(l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_));
v___x_63_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__spec__0(v___x_60_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_();
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_));
v___x_84_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_));
v___x_85_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_));
v___x_86_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4__spec__0(v___x_83_, v___x_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4____boxed(lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_();
return v_res_88_;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__0(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_89_ = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
v___x_90_ = l_Lean_Meta_backward_eqns_nonrecursive;
v___x_91_ = lean_unsigned_to_nat(2u);
v___x_92_ = lean_mk_empty_array_with_capacity(v___x_91_);
v___x_93_ = lean_array_push(v___x_92_, v___x_90_);
v___x_94_ = lean_array_push(v___x_93_, v___x_89_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_Meta_eqnAffectingOptions___closed__0, &l_Lean_Meta_eqnAffectingOptions___closed__0_once, _init_l_Lean_Meta_eqnAffectingOptions___closed__0);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_103_ = lean_string_utf8_byte_size(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_105_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_106_ = lean_string_utf8_byte_size(v_s_104_);
v___x_107_ = lean_obj_once(&l_Lean_Meta_isEqnReservedNameSuffix___closed__0, &l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0);
v___x_108_ = lean_nat_dec_le(v___x_107_, v___x_106_);
if (v___x_108_ == 0)
{
lean_dec_ref(v_s_104_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_string_memcmp(v_s_104_, v___x_105_, v___x_109_, v___x_109_, v___x_107_);
if (v___x_110_ == 0)
{
lean_dec_ref(v_s_104_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_111_ = lean_unsigned_to_nat(3u);
lean_inc_ref(v_s_104_);
v___x_112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_112_, 0, v_s_104_);
lean_ctor_set(v___x_112_, 1, v___x_109_);
lean_ctor_set(v___x_112_, 2, v___x_106_);
v___x_113_ = l_String_Slice_Pos_nextn(v___x_112_, v___x_109_, v___x_111_);
lean_dec_ref(v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v_s_104_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
lean_ctor_set(v___x_114_, 2, v___x_106_);
v___x_115_ = l_String_Slice_isNat(v___x_114_);
lean_dec_ref(v___x_114_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_123_){
_start:
{
uint8_t v___y_125_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_128_ = lean_string_dec_eq(v_s_123_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_130_ = lean_string_dec_eq(v_s_123_, v___x_129_);
v___y_125_ = v___x_130_;
goto v___jp_124_;
}
else
{
v___y_125_ = v___x_128_;
goto v___jp_124_;
}
v___jp_124_:
{
if (v___y_125_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_123_);
return v___x_126_;
}
else
{
lean_dec_ref(v_s_123_);
return v___y_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_Meta_isEqnLikeSuffix(v_s_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_137_, lean_object* v_env_138_, lean_object* v_as_x27_139_, lean_object* v_b_140_){
_start:
{
if (lean_obj_tag(v_as_x27_139_) == 0)
{
lean_dec_ref(v_env_138_);
lean_dec_ref(v_str_137_);
return v_b_140_;
}
else
{
lean_object* v_head_141_; lean_object* v_tail_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref(v_b_140_);
v_head_141_ = lean_ctor_get(v_as_x27_139_, 0);
v_tail_142_ = lean_ctor_get(v_as_x27_139_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_as_x27_139_);
if (v_isSharedCheck_162_ == 0)
{
v___x_144_ = v_as_x27_139_;
v_isShared_145_ = v_isSharedCheck_162_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_tail_142_);
lean_inc(v_head_141_);
lean_dec(v_as_x27_139_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_162_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___y_149_; uint8_t v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_146_ = lean_box(0);
v___x_147_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_157_ = 0;
lean_inc_ref(v_env_138_);
v___x_158_ = l_Lean_Environment_setExporting(v_env_138_, v___x_157_);
lean_inc(v_head_141_);
v___x_159_ = l_Lean_Environment_isSafeDefinition(v___x_158_, v_head_141_);
if (v___x_159_ == 0)
{
v___y_149_ = v___x_159_;
goto v___jp_148_;
}
else
{
uint8_t v___x_160_; 
lean_inc(v_head_141_);
lean_inc_ref(v_env_138_);
v___x_160_ = lean_is_matcher(v_env_138_, v_head_141_);
if (v___x_160_ == 0)
{
v___y_149_ = v___x_159_;
goto v___jp_148_;
}
else
{
lean_del_object(v___x_144_);
lean_dec(v_head_141_);
v_as_x27_139_ = v_tail_142_;
v_b_140_ = v___x_147_;
goto _start;
}
}
v___jp_148_:
{
if (v___y_149_ == 0)
{
lean_del_object(v___x_144_);
lean_dec(v_head_141_);
v_as_x27_139_ = v_tail_142_;
v_b_140_ = v___x_147_;
goto _start;
}
else
{
lean_object* v___x_152_; 
lean_dec(v_tail_142_);
lean_dec_ref(v_env_138_);
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 0);
lean_ctor_set(v___x_144_, 1, v_str_137_);
v___x_152_ = v___x_144_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_head_141_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_str_137_);
v___x_152_ = v_reuseFailAlloc_156_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_146_);
return v___x_155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_163_, lean_object* v_name_164_){
_start:
{
if (lean_obj_tag(v_name_164_) == 1)
{
lean_object* v_pre_165_; lean_object* v_str_166_; uint8_t v___x_167_; 
v_pre_165_ = lean_ctor_get(v_name_164_, 0);
lean_inc(v_pre_165_);
v_str_166_ = lean_ctor_get(v_name_164_, 1);
lean_inc_ref(v_str_166_);
lean_dec_ref(v_name_164_);
lean_inc_ref(v_str_166_);
v___x_167_ = l_Lean_Meta_isEqnLikeSuffix(v_str_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_dec_ref(v_str_166_);
lean_dec(v_pre_165_);
lean_dec_ref(v_env_163_);
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_fst_176_; 
lean_inc(v_pre_165_);
v___x_169_ = l_Lean_privateToUserName(v_pre_165_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v_pre_165_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_box(0);
v___x_174_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_175_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_166_, v_env_163_, v___x_172_, v___x_174_);
v_fst_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_fst_176_);
lean_dec_ref(v___x_175_);
if (lean_obj_tag(v_fst_176_) == 0)
{
return v___x_173_;
}
else
{
lean_object* v_val_177_; 
v_val_177_ = lean_ctor_get(v_fst_176_, 0);
lean_inc(v_val_177_);
lean_dec_ref(v_fst_176_);
return v_val_177_;
}
}
}
else
{
lean_object* v___x_178_; 
lean_dec(v_name_164_);
lean_dec_ref(v_env_163_);
v___x_178_ = lean_box(0);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_179_, lean_object* v_env_180_, lean_object* v_as_181_, lean_object* v_as_x27_182_, lean_object* v_b_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_179_, v_env_180_, v_as_x27_182_, v_b_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_186_, lean_object* v_env_187_, lean_object* v_as_188_, lean_object* v_as_x27_189_, lean_object* v_b_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_186_, v_env_187_, v_as_188_, v_as_x27_189_, v_b_190_, v_a_191_);
lean_dec(v_as_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_193_, lean_object* v_declName_194_, lean_object* v_suffix_195_){
_start:
{
lean_object* v___x_199_; uint8_t v_isModule_200_; 
v___x_199_ = l_Lean_Environment_header(v_env_193_);
v_isModule_200_ = lean_ctor_get_uint8(v___x_199_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_199_);
if (v_isModule_200_ == 0)
{
lean_object* v_name_201_; 
lean_dec_ref(v_env_193_);
v_name_201_ = l_Lean_Name_str___override(v_declName_194_, v_suffix_195_);
return v_name_201_;
}
else
{
uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = 0;
lean_inc_ref(v_env_193_);
v___x_203_ = l_Lean_Environment_setExporting(v_env_193_, v_isModule_200_);
lean_inc(v_declName_194_);
v___x_204_ = l_Lean_Environment_find_x3f(v___x_203_, v_declName_194_, v___x_202_);
if (lean_obj_tag(v___x_204_) == 0)
{
goto v___jp_196_;
}
else
{
lean_object* v_val_205_; uint8_t v___x_206_; 
v_val_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_val_205_);
lean_dec_ref(v___x_204_);
v___x_206_ = l_Lean_ConstantInfo_hasValue(v_val_205_, v___x_202_);
lean_dec(v_val_205_);
if (v___x_206_ == 0)
{
goto v___jp_196_;
}
else
{
lean_object* v_name_207_; 
lean_dec_ref(v_env_193_);
v_name_207_ = l_Lean_Name_str___override(v_declName_194_, v_suffix_195_);
return v_name_207_;
}
}
}
v___jp_196_:
{
lean_object* v_name_197_; lean_object* v___x_198_; 
v_name_197_ = l_Lean_Name_str___override(v_declName_194_, v_suffix_195_);
v___x_198_ = l_Lean_mkPrivateName(v_env_193_, v_name_197_);
lean_dec_ref(v_env_193_);
return v___x_198_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
lean_ctor_set(v___x_213_, 3, v___x_211_);
lean_ctor_set(v___x_213_, 4, v___x_211_);
lean_ctor_set(v___x_213_, 5, v___x_211_);
lean_ctor_set(v___x_213_, 6, v___x_211_);
lean_ctor_set(v___x_213_, 7, v___x_211_);
lean_ctor_set(v___x_213_, 8, v___x_211_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(32u);
v___x_215_ = lean_mk_empty_array_with_capacity(v___x_214_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = ((size_t)5ULL);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_unsigned_to_nat(32u);
v___x_220_ = lean_mk_empty_array_with_capacity(v___x_219_);
v___x_221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_222_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_218_);
lean_ctor_set(v___x_222_, 3, v___x_218_);
lean_ctor_set_usize(v___x_222_, 4, v___x_217_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = lean_box(1);
v___x_224_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_225_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_223_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; lean_object* v_env_232_; lean_object* v_options_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_231_ = lean_st_ref_get(v___y_229_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_232_);
lean_dec(v___x_231_);
v_options_233_ = lean_ctor_get(v___y_228_, 2);
v___x_234_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_235_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_233_);
v___x_236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_236_, 0, v_env_232_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_ctor_set(v___x_236_, 3, v_options_233_);
v___x_237_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v_msgData_227_);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_ref_248_; lean_object* v___x_249_; lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_258_; 
v_ref_248_ = lean_ctor_get(v___y_245_, 5);
v___x_249_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_244_, v___y_245_, v___y_246_);
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_258_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_258_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_258_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
lean_inc(v_ref_248_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_ref_248_);
lean_ctor_set(v___x_254_, 1, v_a_250_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 1);
lean_ctor_set(v___x_252_, 0, v___x_254_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_263_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_273_, lean_object* v_reservedName_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_278_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_279_ = 0;
v___x_280_ = l_Lean_MessageData_ofConstName(v_declName_273_, v___x_279_);
v___x_281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_278_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = 1;
v___x_285_ = l_Lean_MessageData_ofConstName(v_reservedName_274_, v___x_284_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_283_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_288_, v___y_275_, v___y_276_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_290_, lean_object* v_reservedName_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_290_, v_reservedName_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_296_, lean_object* v_suffix_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v_reservedName_303_; uint8_t v___x_304_; uint8_t v___x_305_; 
v___x_301_ = lean_st_ref_get(v___y_299_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_env_302_);
lean_dec(v___x_301_);
lean_inc(v_declName_296_);
v_reservedName_303_ = l_Lean_Name_str___override(v_declName_296_, v_suffix_297_);
v___x_304_ = 1;
lean_inc(v_reservedName_303_);
v___x_305_ = l_Lean_Environment_contains(v_env_302_, v_reservedName_303_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_reservedName_303_);
lean_dec(v_declName_296_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_296_, v_reservedName_303_, v___y_298_, v___y_299_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_309_, lean_object* v_suffix_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_309_, v_suffix_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_315_);
v___x_320_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_315_, v___x_319_, v_a_316_, v_a_317_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v___x_320_);
v___x_321_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_315_);
v___x_322_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_315_, v___x_321_, v_a_316_, v_a_317_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v___x_322_);
v___x_323_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_324_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_315_, v___x_323_, v_a_316_, v_a_317_);
return v___x_324_;
}
else
{
lean_dec(v_declName_315_);
return v___x_322_;
}
}
else
{
lean_dec(v_declName_315_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_331_, v___y_332_, v___y_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_336_, v_msg_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_341_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_342_, lean_object* v_n_343_){
_start:
{
lean_object* v___x_344_; 
lean_inc(v_n_343_);
lean_inc_ref(v_env_342_);
v___x_344_ = l_Lean_Meta_declFromEqLikeName(v_env_342_, v_n_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; lean_object* v_fst_346_; lean_object* v_snd_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref(v___x_344_);
v_fst_346_ = lean_ctor_get(v_val_345_, 0);
lean_inc(v_fst_346_);
v_snd_347_ = lean_ctor_get(v_val_345_, 1);
lean_inc(v_snd_347_);
lean_dec(v_val_345_);
v___x_348_ = l_Lean_Meta_mkEqLikeNameFor(v_env_342_, v_fst_346_, v_snd_347_);
v___x_349_ = lean_name_eq(v_n_343_, v___x_348_);
lean_dec(v___x_348_);
lean_dec(v_n_343_);
return v___x_349_;
}
else
{
uint8_t v___x_350_; 
lean_dec(v___x_344_);
lean_dec(v_n_343_);
lean_dec_ref(v_env_342_);
v___x_350_ = 0;
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_351_, lean_object* v_n_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_351_, v_n_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_357_; lean_object* v___x_358_; 
v___f_357_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_358_ = l_Lean_registerReservedNamePredicate(v___f_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_box(0);
v___x_363_ = lean_st_mk_ref(v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_369_ = lean_mk_io_user_error(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_initializing();
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_389_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_389_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_389_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_389_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
uint8_t v___x_377_; 
v___x_377_ = lean_unbox(v_a_373_);
lean_dec(v_a_373_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_380_; 
lean_dec_ref(v_f_370_);
v___x_378_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 1);
lean_ctor_set(v___x_375_, 0, v___x_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_382_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_383_ = lean_st_ref_take(v___x_382_);
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v_f_370_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_st_ref_set(v___x_382_, v___x_384_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_385_);
v___x_387_ = v___x_375_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v_f_370_);
v_a_390_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_372_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_372_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_registerGetEqnsFn(v_f_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_411_; lean_object* v_env_412_; uint8_t v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_st_ref_get(v_a_405_);
v_env_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_env_412_);
lean_dec(v___x_411_);
v___x_413_ = 0;
lean_inc(v_declName_401_);
v___x_414_ = l_Lean_Environment_findAsync_x3f(v_env_412_, v_declName_401_, v___x_413_);
if (lean_obj_tag(v___x_414_) == 1)
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_446_; 
v_val_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_446_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_446_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_446_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
uint8_t v_kind_419_; 
v_kind_419_ = lean_ctor_get_uint8(v_val_415_, sizeof(void*)*3);
if (v_kind_419_ == 0)
{
lean_object* v_sig_420_; lean_object* v___x_421_; lean_object* v_env_422_; uint8_t v___x_423_; 
v_sig_420_ = lean_ctor_get(v_val_415_, 1);
lean_inc_ref(v_sig_420_);
lean_dec(v_val_415_);
v___x_421_ = lean_st_ref_get(v_a_405_);
v_env_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_env_422_);
lean_dec(v___x_421_);
v___x_423_ = lean_is_matcher(v_env_422_, v_declName_401_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v_type_425_; lean_object* v___x_426_; 
lean_del_object(v___x_417_);
v___x_424_ = lean_task_get_own(v_sig_420_);
v_type_425_ = lean_ctor_get(v___x_424_, 2);
lean_inc_ref(v_type_425_);
lean_dec(v___x_424_);
v___x_426_ = l_Lean_Meta_isProp(v_type_425_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_441_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_441_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint8_t v___x_431_; 
v___x_431_ = lean_unbox(v_a_427_);
lean_dec(v_a_427_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_432_ = 1;
v___x_433_ = lean_box(v___x_432_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_433_);
v___x_435_ = v___x_429_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_box(v___x_423_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_437_);
v___x_439_ = v___x_429_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
return v___x_426_;
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_444_; 
lean_dec_ref(v_sig_420_);
v___x_442_ = lean_box(v___x_413_);
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 0);
lean_ctor_set(v___x_417_, 0, v___x_442_);
v___x_444_ = v___x_417_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_del_object(v___x_417_);
lean_dec(v_val_415_);
lean_dec(v_declName_401_);
goto v___jp_407_;
}
}
}
else
{
lean_dec(v___x_414_);
lean_dec(v_declName_401_);
goto v___jp_407_;
}
v___jp_407_:
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = 0;
v___x_409_ = lean_box(v___x_408_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_453_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_462_);
return v_res_464_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_465_; lean_object* v___f_466_; 
v___x_465_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_466_ = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_466_, 0, v___x_465_);
return v___f_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___f_468_ = lean_obj_once(&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_box(1);
v___x_471_ = l_Lean_registerEnvExtension___redArg(v___f_468_, v___x_469_, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; lean_object* v_env_478_; lean_object* v_toConstantVal_479_; lean_object* v_value_480_; lean_object* v_all_481_; uint8_t v___y_483_; lean_object* v_type_491_; uint8_t v___x_492_; 
v___x_477_ = lean_st_ref_get(v___y_475_);
v_env_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_env_478_);
lean_dec(v___x_477_);
v_toConstantVal_479_ = lean_ctor_get(v_thm_474_, 0);
v_value_480_ = lean_ctor_get(v_thm_474_, 1);
v_all_481_ = lean_ctor_get(v_thm_474_, 2);
v_type_491_ = lean_ctor_get(v_toConstantVal_479_, 2);
lean_inc_ref(v_env_478_);
v___x_492_ = l_Lean_Environment_hasUnsafe(v_env_478_, v_type_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = l_Lean_Environment_hasUnsafe(v_env_478_, v_value_480_);
v___y_483_ = v___x_493_;
goto v___jp_482_;
}
else
{
lean_dec_ref(v_env_478_);
v___y_483_ = v___x_492_;
goto v___jp_482_;
}
v___jp_482_:
{
if (v___y_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_484_, 0, v_thm_474_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_inc(v_all_481_);
lean_inc_ref(v_value_480_);
lean_inc_ref(v_toConstantVal_479_);
lean_dec_ref(v_thm_474_);
v___x_486_ = lean_box(0);
v___x_487_ = 0;
v___x_488_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_488_, 0, v_toConstantVal_479_);
lean_ctor_set(v___x_488_, 1, v_value_480_);
lean_ctor_set(v___x_488_, 2, v___x_486_);
lean_ctor_set(v___x_488_, 3, v_all_481_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*4, v___x_487_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_494_, v___y_495_);
lean_dec(v___y_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_498_, v___y_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_512_, lean_object* v_b_513_, lean_object* v_c_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; 
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
v___x_520_ = lean_apply_7(v_k_512_, v_b_513_, v_c_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, lean_box(0));
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_521_, lean_object* v_b_522_, lean_object* v_c_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_521_, v_b_522_, v_c_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_530_, lean_object* v_k_531_, uint8_t v_cleanupAnnotations_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___f_538_; uint8_t v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___f_538_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_538_, 0, v_k_531_);
v___x_539_ = 1;
v___x_540_ = 0;
v___x_541_ = lean_box(0);
v___x_542_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_530_, v___x_539_, v___x_540_, v___x_539_, v___x_540_, v___x_541_, v___f_538_, v_cleanupAnnotations_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_542_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_542_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_559_, lean_object* v_k_560_, lean_object* v_cleanupAnnotations_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_567_; lean_object* v_res_568_; 
v_cleanupAnnotations_boxed_567_ = lean_unbox(v_cleanupAnnotations_561_);
v_res_568_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_559_, v_k_560_, v_cleanupAnnotations_boxed_567_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_569_, lean_object* v_e_570_, lean_object* v_k_571_, uint8_t v_cleanupAnnotations_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_570_, v_k_571_, v_cleanupAnnotations_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_579_, lean_object* v_e_580_, lean_object* v_k_581_, lean_object* v_cleanupAnnotations_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_588_; lean_object* v_res_589_; 
v_cleanupAnnotations_boxed_588_ = lean_unbox(v_cleanupAnnotations_582_);
v_res_589_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_579_, v_e_580_, v_k_581_, v_cleanupAnnotations_boxed_588_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
if (lean_obj_tag(v_a_590_) == 0)
{
lean_object* v___x_592_; 
v___x_592_ = l_List_reverse___redArg(v_a_591_);
return v___x_592_;
}
else
{
lean_object* v_head_593_; lean_object* v_tail_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
v_head_593_ = lean_ctor_get(v_a_590_, 0);
v_tail_594_ = lean_ctor_get(v_a_590_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_a_590_);
if (v_isSharedCheck_603_ == 0)
{
v___x_596_ = v_a_590_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_tail_594_);
lean_inc(v_head_593_);
lean_dec(v_a_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = l_Lean_mkLevelParam(v_head_593_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v_a_591_);
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_a_591_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
v_a_590_ = v_tail_594_;
v_a_591_ = v___x_600_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_604_, lean_object* v_name_605_, lean_object* v_xs_606_, lean_object* v_body_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_name_613_; lean_object* v_levelParams_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_684_; 
v_name_613_ = lean_ctor_get(v_toConstantVal_604_, 0);
v_levelParams_614_ = lean_ctor_get(v_toConstantVal_604_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_toConstantVal_604_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_toConstantVal_604_, 2);
lean_dec(v_unused_685_);
v___x_616_ = v_toConstantVal_604_;
v_isShared_617_ = v_isSharedCheck_684_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_levelParams_614_);
lean_inc(v_name_613_);
lean_dec(v_toConstantVal_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_684_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_lhs_621_; lean_object* v___x_622_; 
v___x_618_ = lean_box(0);
lean_inc(v_levelParams_614_);
v___x_619_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_614_, v___x_618_);
v___x_620_ = l_Lean_mkConst(v_name_613_, v___x_619_);
v_lhs_621_ = l_Lean_mkAppN(v___x_620_, v_xs_606_);
lean_inc_ref(v_lhs_621_);
v___x_622_ = l_Lean_Meta_mkEq(v_lhs_621_, v_body_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; uint8_t v___x_624_; uint8_t v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref(v___x_622_);
v___x_624_ = 0;
v___x_625_ = 1;
v___x_626_ = 1;
v___x_627_ = l_Lean_Meta_mkForallFVars(v_xs_606_, v_a_623_, v___x_624_, v___x_625_, v___x_625_, v___x_626_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_629_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref(v___x_627_);
v___x_629_ = l_Lean_Meta_letToHave(v_a_628_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref(v___x_629_);
v___x_631_ = l_Lean_Meta_mkEqRefl(v_lhs_621_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = l_Lean_Meta_mkLambdaFVars(v_xs_606_, v_a_632_, v___x_624_, v___x_625_, v___x_624_, v___x_625_, v___x_626_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
lean_inc(v_name_605_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 2, v_a_630_);
lean_ctor_set(v___x_616_, 0, v_name_605_);
v___x_636_ = v___x_616_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_name_605_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_levelParams_614_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_a_630_);
v___x_636_ = v_reuseFailAlloc_643_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_a_640_; lean_object* v___x_641_; 
lean_inc(v_name_605_);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v_name_605_);
lean_ctor_set(v___x_637_, 1, v___x_618_);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v_a_634_);
lean_ctor_set(v___x_638_, 2, v___x_637_);
v___x_639_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_638_, v___y_611_);
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = l_Lean_addDecl(v_a_640_, v___x_624_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v___x_642_; 
lean_dec_ref(v___x_641_);
v___x_642_ = l_Lean_inferDefEqAttr(v_name_605_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
return v___x_642_;
}
else
{
lean_dec(v_name_605_);
return v___x_641_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_a_630_);
lean_del_object(v___x_616_);
lean_dec(v_levelParams_614_);
lean_dec(v_name_605_);
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
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_630_);
lean_del_object(v___x_616_);
lean_dec(v_levelParams_614_);
lean_dec(v_name_605_);
v_a_652_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_631_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_631_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_lhs_621_);
lean_del_object(v___x_616_);
lean_dec(v_levelParams_614_);
lean_dec(v_name_605_);
v_a_660_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_629_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_629_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_lhs_621_);
lean_del_object(v___x_616_);
lean_dec(v_levelParams_614_);
lean_dec(v_name_605_);
v_a_668_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_627_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_627_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_lhs_621_);
lean_del_object(v___x_616_);
lean_dec(v_levelParams_614_);
lean_dec(v_name_605_);
v_a_676_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_622_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_622_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_686_, lean_object* v_name_687_, lean_object* v_xs_688_, lean_object* v_body_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_686_, v_name_687_, v_xs_688_, v_body_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec_ref(v_xs_688_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_696_, lean_object* v_info_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_toConstantVal_703_; lean_object* v_value_704_; lean_object* v___f_705_; uint8_t v___x_706_; lean_object* v___x_707_; 
v_toConstantVal_703_ = lean_ctor_get(v_info_697_, 0);
lean_inc_ref(v_toConstantVal_703_);
v_value_704_ = lean_ctor_get(v_info_697_, 1);
lean_inc_ref(v_value_704_);
lean_dec_ref(v_info_697_);
v___f_705_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_705_, 0, v_toConstantVal_703_);
lean_closure_set(v___f_705_, 1, v_name_696_);
v___x_706_ = 1;
v___x_707_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_704_, v___f_705_, v___x_706_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_708_, lean_object* v_info_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_708_, v_info_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_716_, lean_object* v_name_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_726_; lean_object* v_env_727_; uint8_t v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_st_ref_get(v_a_721_);
v_env_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_env_727_);
lean_dec(v___x_726_);
v___x_728_ = 0;
lean_inc(v_declName_716_);
v___x_729_ = l_Lean_Environment_find_x3f(v_env_727_, v_declName_716_, v___x_728_);
if (lean_obj_tag(v___x_729_) == 1)
{
lean_object* v_val_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_756_; 
v_val_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_756_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_756_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_val_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_756_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
if (lean_obj_tag(v_val_730_) == 1)
{
lean_object* v_val_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_val_734_ = lean_ctor_get(v_val_730_, 0);
lean_inc_ref(v_val_734_);
lean_dec_ref(v_val_730_);
lean_inc(v_name_717_);
v___x_735_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_735_, 0, v_name_717_);
lean_closure_set(v___x_735_, 1, v_val_734_);
lean_inc_ref(v_a_720_);
lean_inc(v_name_717_);
v___x_736_ = l_Lean_Meta_realizeConst(v_declName_716_, v_name_717_, v___x_735_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_746_; 
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v___x_736_, 0);
lean_dec(v_unused_747_);
v___x_738_ = v___x_736_;
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
else
{
lean_dec(v___x_736_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_746_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v_name_717_);
v___x_741_ = v___x_732_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_name_717_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_del_object(v___x_732_);
lean_dec(v_name_717_);
v_a_748_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_736_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_736_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec(v_name_717_);
lean_dec(v_declName_716_);
goto v___jp_723_;
}
}
}
else
{
lean_dec(v___x_729_);
lean_dec(v_name_717_);
lean_dec(v_declName_716_);
goto v___jp_723_;
}
v___jp_723_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_757_, lean_object* v_name_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Meta_mkSimpleEqThm(v_declName_757_, v_name_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_765_, lean_object* v_vals_766_, lean_object* v_i_767_, lean_object* v_k_768_){
_start:
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_array_get_size(v_keys_765_);
v___x_770_ = lean_nat_dec_lt(v_i_767_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
lean_dec(v_i_767_);
v___x_771_ = lean_box(0);
return v___x_771_;
}
else
{
lean_object* v_k_x27_772_; uint8_t v___x_773_; 
v_k_x27_772_ = lean_array_fget_borrowed(v_keys_765_, v_i_767_);
v___x_773_ = lean_name_eq(v_k_768_, v_k_x27_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_add(v_i_767_, v___x_774_);
lean_dec(v_i_767_);
v_i_767_ = v___x_775_;
goto _start;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_array_fget_borrowed(v_vals_766_, v_i_767_);
lean_dec(v_i_767_);
lean_inc(v___x_777_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_779_, lean_object* v_vals_780_, lean_object* v_i_781_, lean_object* v_k_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_779_, v_vals_780_, v_i_781_, v_k_782_);
lean_dec(v_k_782_);
lean_dec_ref(v_vals_780_);
lean_dec_ref(v_keys_779_);
return v_res_783_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; 
v___x_784_ = ((size_t)5ULL);
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_shift_left(v___x_785_, v___x_784_);
return v___x_786_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; 
v___x_787_ = ((size_t)1ULL);
v___x_788_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_789_ = lean_usize_sub(v___x_788_, v___x_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_790_, size_t v_x_791_, lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_790_) == 0)
{
lean_object* v_es_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_814_; 
v_es_793_ = lean_ctor_get(v_x_790_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_790_);
if (v_isSharedCheck_814_ == 0)
{
v___x_795_ = v_x_790_;
v_isShared_796_ = v_isSharedCheck_814_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_es_793_);
lean_dec(v_x_790_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_814_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; lean_object* v_j_801_; lean_object* v___x_802_; 
v___x_797_ = lean_box(2);
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_800_ = lean_usize_land(v_x_791_, v___x_799_);
v_j_801_ = lean_usize_to_nat(v___x_800_);
v___x_802_ = lean_array_get(v___x_797_, v_es_793_, v_j_801_);
lean_dec(v_j_801_);
lean_dec_ref(v_es_793_);
switch(lean_obj_tag(v___x_802_))
{
case 0:
{
lean_object* v_key_803_; lean_object* v_val_804_; uint8_t v___x_805_; 
v_key_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_key_803_);
v_val_804_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_val_804_);
lean_dec_ref(v___x_802_);
v___x_805_ = lean_name_eq(v_x_792_, v_key_803_);
lean_dec(v_key_803_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec(v_val_804_);
lean_del_object(v___x_795_);
v___x_806_ = lean_box(0);
return v___x_806_;
}
else
{
lean_object* v___x_808_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 1);
lean_ctor_set(v___x_795_, 0, v_val_804_);
v___x_808_ = v___x_795_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_804_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
case 1:
{
lean_object* v_node_810_; size_t v___x_811_; 
lean_del_object(v___x_795_);
v_node_810_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_node_810_);
lean_dec_ref(v___x_802_);
v___x_811_ = lean_usize_shift_right(v_x_791_, v___x_798_);
v_x_790_ = v_node_810_;
v_x_791_ = v___x_811_;
goto _start;
}
default: 
{
lean_object* v___x_813_; 
lean_del_object(v___x_795_);
v___x_813_ = lean_box(0);
return v___x_813_;
}
}
}
}
else
{
lean_object* v_ks_815_; lean_object* v_vs_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_ks_815_ = lean_ctor_get(v_x_790_, 0);
lean_inc_ref(v_ks_815_);
v_vs_816_ = lean_ctor_get(v_x_790_, 1);
lean_inc_ref(v_vs_816_);
lean_dec_ref(v_x_790_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_815_, v_vs_816_, v___x_817_, v_x_792_);
lean_dec_ref(v_vs_816_);
lean_dec_ref(v_ks_815_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
size_t v_x_355__boxed_822_; lean_object* v_res_823_; 
v_x_355__boxed_822_ = lean_unbox_usize(v_x_820_);
lean_dec(v_x_820_);
v_res_823_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_819_, v_x_355__boxed_822_, v_x_821_);
lean_dec(v_x_821_);
return v_res_823_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_824_; uint64_t v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(1723u);
v___x_825_ = lean_uint64_of_nat(v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
uint64_t v___y_829_; 
if (lean_obj_tag(v_x_827_) == 0)
{
uint64_t v___x_832_; 
v___x_832_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_829_ = v___x_832_;
goto v___jp_828_;
}
else
{
uint64_t v_hash_833_; 
v_hash_833_ = lean_ctor_get_uint64(v_x_827_, sizeof(void*)*2);
v___y_829_ = v_hash_833_;
goto v___jp_828_;
}
v___jp_828_:
{
size_t v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_uint64_to_usize(v___y_829_);
v___x_831_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_826_, v___x_830_, v_x_827_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_834_, v_x_835_);
lean_dec(v_x_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; lean_object* v_env_841_; lean_object* v___x_842_; lean_object* v_asyncMode_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_840_ = lean_st_ref_get(v_a_838_);
v_env_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref(v_env_841_);
lean_dec(v___x_840_);
v___x_842_ = l_Lean_Meta_eqnsExt;
v_asyncMode_843_ = lean_ctor_get(v___x_842_, 2);
lean_inc(v_asyncMode_843_);
v___x_844_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_845_ = lean_box(0);
v___x_846_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_844_, v___x_842_, v_env_841_, v_asyncMode_843_, v___x_845_);
lean_dec(v_asyncMode_843_);
v___x_847_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_846_, v_thmName_837_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec(v_thmName_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_853_, v_a_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_thmName_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_867_, v_x_868_, v_x_869_);
lean_dec(v_x_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, size_t v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_872_, v_x_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
size_t v_x_472__boxed_880_; lean_object* v_res_881_; 
v_x_472__boxed_880_ = lean_unbox_usize(v_x_878_);
lean_dec(v_x_878_);
v_res_881_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_876_, v_x_877_, v_x_472__boxed_880_, v_x_879_);
lean_dec(v_x_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_882_, lean_object* v_keys_883_, lean_object* v_vals_884_, lean_object* v_heq_885_, lean_object* v_i_886_, lean_object* v_k_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_883_, v_vals_884_, v_i_886_, v_k_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_889_, lean_object* v_keys_890_, lean_object* v_vals_891_, lean_object* v_heq_892_, lean_object* v_i_893_, lean_object* v_k_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_889_, v_keys_890_, v_vals_891_, v_heq_892_, v_i_893_, v_k_894_);
lean_dec(v_k_894_);
lean_dec_ref(v_vals_891_);
lean_dec_ref(v_keys_890_);
return v_res_895_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_896_, lean_object* v_i_897_, lean_object* v_k_898_){
_start:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_array_get_size(v_keys_896_);
v___x_900_ = lean_nat_dec_lt(v_i_897_, v___x_899_);
if (v___x_900_ == 0)
{
lean_dec(v_i_897_);
return v___x_900_;
}
else
{
lean_object* v_k_x27_901_; uint8_t v___x_902_; 
v_k_x27_901_ = lean_array_fget_borrowed(v_keys_896_, v_i_897_);
v___x_902_ = lean_name_eq(v_k_898_, v_k_x27_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_add(v_i_897_, v___x_903_);
lean_dec(v_i_897_);
v_i_897_ = v___x_904_;
goto _start;
}
else
{
lean_dec(v_i_897_);
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_906_, lean_object* v_i_907_, lean_object* v_k_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_906_, v_i_907_, v_k_908_);
lean_dec(v_k_908_);
lean_dec_ref(v_keys_906_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_911_, size_t v_x_912_, lean_object* v_x_913_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_object* v_es_914_; lean_object* v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v_j_919_; lean_object* v___x_920_; 
v_es_914_ = lean_ctor_get(v_x_911_, 0);
lean_inc_ref(v_es_914_);
lean_dec_ref(v_x_911_);
v___x_915_ = lean_box(2);
v___x_916_ = ((size_t)5ULL);
v___x_917_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_918_ = lean_usize_land(v_x_912_, v___x_917_);
v_j_919_ = lean_usize_to_nat(v___x_918_);
v___x_920_ = lean_array_get(v___x_915_, v_es_914_, v_j_919_);
lean_dec(v_j_919_);
lean_dec_ref(v_es_914_);
switch(lean_obj_tag(v___x_920_))
{
case 0:
{
lean_object* v_key_921_; uint8_t v___x_922_; 
v_key_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_key_921_);
lean_dec_ref(v___x_920_);
v___x_922_ = lean_name_eq(v_x_913_, v_key_921_);
lean_dec(v_key_921_);
return v___x_922_;
}
case 1:
{
lean_object* v_node_923_; size_t v___x_924_; 
v_node_923_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_node_923_);
lean_dec_ref(v___x_920_);
v___x_924_ = lean_usize_shift_right(v_x_912_, v___x_916_);
v_x_911_ = v_node_923_;
v_x_912_ = v___x_924_;
goto _start;
}
default: 
{
uint8_t v___x_926_; 
v___x_926_ = 0;
return v___x_926_;
}
}
}
else
{
lean_object* v_ks_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_ks_927_ = lean_ctor_get(v_x_911_, 0);
lean_inc_ref(v_ks_927_);
lean_dec_ref(v_x_911_);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_927_, v___x_928_, v_x_913_);
lean_dec_ref(v_ks_927_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
size_t v_x_335__boxed_933_; uint8_t v_res_934_; lean_object* v_r_935_; 
v_x_335__boxed_933_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_res_934_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_930_, v_x_335__boxed_933_, v_x_932_);
lean_dec(v_x_932_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
uint64_t v___y_939_; 
if (lean_obj_tag(v_x_937_) == 0)
{
uint64_t v___x_942_; 
v___x_942_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_939_ = v___x_942_;
goto v___jp_938_;
}
else
{
uint64_t v_hash_943_; 
v_hash_943_ = lean_ctor_get_uint64(v_x_937_, sizeof(void*)*2);
v___y_939_ = v_hash_943_;
goto v___jp_938_;
}
v___jp_938_:
{
size_t v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_uint64_to_usize(v___y_939_);
v___x_941_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_936_, v___x_940_, v_x_937_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_944_, v_x_945_);
lean_dec(v_x_945_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; lean_object* v_env_952_; lean_object* v___x_953_; lean_object* v_asyncMode_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_951_ = lean_st_ref_get(v_a_949_);
v_env_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc_ref(v_env_952_);
lean_dec(v___x_951_);
v___x_953_ = l_Lean_Meta_eqnsExt;
v_asyncMode_954_ = lean_ctor_get(v___x_953_, 2);
lean_inc(v_asyncMode_954_);
v___x_955_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_956_ = lean_box(0);
v___x_957_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_955_, v___x_953_, v_env_952_, v_asyncMode_954_, v___x_956_);
lean_dec(v_asyncMode_954_);
v___x_958_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_957_, v_thmName_948_);
v___x_959_ = lean_box(v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec(v_thmName_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_965_, v_a_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Meta_isEqnThm(v_thmName_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_thmName_970_);
return v_res_974_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_976_, v_x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
uint8_t v_res_982_; lean_object* v_r_983_; 
v_res_982_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_979_, v_x_980_, v_x_981_);
lean_dec(v_x_981_);
v_r_983_ = lean_box(v_res_982_);
return v_r_983_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_984_, lean_object* v_x_985_, size_t v_x_986_, lean_object* v_x_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_985_, v_x_986_, v_x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
size_t v_x_429__boxed_993_; uint8_t v_res_994_; lean_object* v_r_995_; 
v_x_429__boxed_993_ = lean_unbox_usize(v_x_991_);
lean_dec(v_x_991_);
v_res_994_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_989_, v_x_990_, v_x_429__boxed_993_, v_x_992_);
lean_dec(v_x_992_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_996_, lean_object* v_keys_997_, lean_object* v_vals_998_, lean_object* v_heq_999_, lean_object* v_i_1000_, lean_object* v_k_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_997_, v_i_1000_, v_k_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_keys_1004_, lean_object* v_vals_1005_, lean_object* v_heq_1006_, lean_object* v_i_1007_, lean_object* v_k_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1003_, v_keys_1004_, v_vals_1005_, v_heq_1006_, v_i_1007_, v_k_1008_);
lean_dec(v_k_1008_);
lean_dec_ref(v_vals_1005_);
lean_dec_ref(v_keys_1004_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v_ks_1015_; lean_object* v_vs_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1040_; 
v_ks_1015_ = lean_ctor_get(v_x_1011_, 0);
v_vs_1016_ = lean_ctor_get(v_x_1011_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_x_1011_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1018_ = v_x_1011_;
v_isShared_1019_ = v_isSharedCheck_1040_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_vs_1016_);
lean_inc(v_ks_1015_);
lean_dec(v_x_1011_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1040_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_array_get_size(v_ks_1015_);
v___x_1021_ = lean_nat_dec_lt(v_x_1012_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec(v_x_1012_);
v___x_1022_ = lean_array_push(v_ks_1015_, v_x_1013_);
v___x_1023_ = lean_array_push(v_vs_1016_, v_x_1014_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1023_);
lean_ctor_set(v___x_1018_, 0, v___x_1022_);
v___x_1025_ = v___x_1018_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
else
{
lean_object* v_k_x27_1027_; uint8_t v___x_1028_; 
v_k_x27_1027_ = lean_array_fget_borrowed(v_ks_1015_, v_x_1012_);
v___x_1028_ = lean_name_eq(v_x_1013_, v_k_x27_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1030_; 
if (v_isShared_1019_ == 0)
{
v___x_1030_ = v___x_1018_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_ks_1015_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_vs_1016_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(1u);
v___x_1032_ = lean_nat_add(v_x_1012_, v___x_1031_);
lean_dec(v_x_1012_);
v_x_1011_ = v___x_1030_;
v_x_1012_ = v___x_1032_;
goto _start;
}
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1035_ = lean_array_fset(v_ks_1015_, v_x_1012_, v_x_1013_);
v___x_1036_ = lean_array_fset(v_vs_1016_, v_x_1012_, v_x_1014_);
lean_dec(v_x_1012_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1036_);
lean_ctor_set(v___x_1018_, 0, v___x_1035_);
v___x_1038_ = v___x_1018_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1041_, lean_object* v_k_1042_, lean_object* v_v_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1041_, v___x_1044_, v_k_1042_, v_v_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1047_, size_t v_x_1048_, size_t v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v_es_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v_j_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_es_1052_ = lean_ctor_get(v_x_1047_, 0);
v___x_1053_ = ((size_t)5ULL);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1056_ = lean_usize_land(v_x_1048_, v___x_1055_);
v_j_1057_ = lean_usize_to_nat(v___x_1056_);
v___x_1058_ = lean_array_get_size(v_es_1052_);
v___x_1059_ = lean_nat_dec_lt(v_j_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec(v_j_1057_);
lean_dec(v_x_1051_);
lean_dec(v_x_1050_);
return v_x_1047_;
}
else
{
lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1096_; 
lean_inc_ref(v_es_1052_);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_x_1047_, 0);
lean_dec(v_unused_1097_);
v___x_1061_ = v_x_1047_;
v_isShared_1062_ = v_isSharedCheck_1096_;
goto v_resetjp_1060_;
}
else
{
lean_dec(v_x_1047_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1096_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_v_1063_; lean_object* v___x_1064_; lean_object* v_xs_x27_1065_; lean_object* v___y_1067_; 
v_v_1063_ = lean_array_fget(v_es_1052_, v_j_1057_);
v___x_1064_ = lean_box(0);
v_xs_x27_1065_ = lean_array_fset(v_es_1052_, v_j_1057_, v___x_1064_);
switch(lean_obj_tag(v_v_1063_))
{
case 0:
{
lean_object* v_key_1072_; lean_object* v_val_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1083_; 
v_key_1072_ = lean_ctor_get(v_v_1063_, 0);
v_val_1073_ = lean_ctor_get(v_v_1063_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_v_1063_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1075_ = v_v_1063_;
v_isShared_1076_ = v_isSharedCheck_1083_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_val_1073_);
lean_inc(v_key_1072_);
lean_dec(v_v_1063_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1083_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_name_eq(v_x_1050_, v_key_1072_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_del_object(v___x_1075_);
v___x_1078_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1072_, v_val_1073_, v_x_1050_, v_x_1051_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
v___y_1067_ = v___x_1079_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1081_; 
lean_dec(v_val_1073_);
lean_dec(v_key_1072_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v_x_1051_);
lean_ctor_set(v___x_1075_, 0, v_x_1050_);
v___x_1081_ = v___x_1075_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_x_1050_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_x_1051_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
v___y_1067_ = v___x_1081_;
goto v___jp_1066_;
}
}
}
}
case 1:
{
lean_object* v_node_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1094_; 
v_node_1084_ = lean_ctor_get(v_v_1063_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_v_1063_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1086_ = v_v_1063_;
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_node_1084_);
lean_dec(v_v_1063_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1088_ = lean_usize_shift_right(v_x_1048_, v___x_1053_);
v___x_1089_ = lean_usize_add(v_x_1049_, v___x_1054_);
v___x_1090_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1084_, v___x_1088_, v___x_1089_, v_x_1050_, v_x_1051_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1090_);
v___x_1092_ = v___x_1086_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
v___y_1067_ = v___x_1092_;
goto v___jp_1066_;
}
}
}
default: 
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_x_1050_);
lean_ctor_set(v___x_1095_, 1, v_x_1051_);
v___y_1067_ = v___x_1095_;
goto v___jp_1066_;
}
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_array_fset(v_xs_x27_1065_, v_j_1057_, v___y_1067_);
lean_dec(v_j_1057_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1068_);
v___x_1070_ = v___x_1061_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
else
{
lean_object* v_ks_1098_; lean_object* v_vs_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1119_; 
v_ks_1098_ = lean_ctor_get(v_x_1047_, 0);
v_vs_1099_ = lean_ctor_get(v_x_1047_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1101_ = v_x_1047_;
v_isShared_1102_ = v_isSharedCheck_1119_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_vs_1099_);
lean_inc(v_ks_1098_);
lean_dec(v_x_1047_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1119_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_ks_1098_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_vs_1099_);
v___x_1104_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v_newNode_1105_; uint8_t v___y_1107_; size_t v___x_1113_; uint8_t v___x_1114_; 
v_newNode_1105_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1104_, v_x_1050_, v_x_1051_);
v___x_1113_ = ((size_t)7ULL);
v___x_1114_ = lean_usize_dec_le(v___x_1113_, v_x_1049_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1115_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1105_);
v___x_1116_ = lean_unsigned_to_nat(4u);
v___x_1117_ = lean_nat_dec_lt(v___x_1115_, v___x_1116_);
lean_dec(v___x_1115_);
v___y_1107_ = v___x_1117_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v___x_1114_;
goto v___jp_1106_;
}
v___jp_1106_:
{
if (v___y_1107_ == 0)
{
lean_object* v_ks_1108_; lean_object* v_vs_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_ks_1108_ = lean_ctor_get(v_newNode_1105_, 0);
lean_inc_ref(v_ks_1108_);
v_vs_1109_ = lean_ctor_get(v_newNode_1105_, 1);
lean_inc_ref(v_vs_1109_);
lean_dec_ref(v_newNode_1105_);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1112_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1049_, v_ks_1108_, v_vs_1109_, v___x_1110_, v___x_1111_);
lean_dec_ref(v_vs_1109_);
lean_dec_ref(v_ks_1108_);
return v___x_1112_;
}
else
{
return v_newNode_1105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1120_, lean_object* v_keys_1121_, lean_object* v_vals_1122_, lean_object* v_i_1123_, lean_object* v_entries_1124_){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_array_get_size(v_keys_1121_);
v___x_1126_ = lean_nat_dec_lt(v_i_1123_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_dec(v_i_1123_);
return v_entries_1124_;
}
else
{
lean_object* v_k_1127_; lean_object* v_v_1128_; uint64_t v___y_1130_; 
v_k_1127_ = lean_array_fget_borrowed(v_keys_1121_, v_i_1123_);
v_v_1128_ = lean_array_fget_borrowed(v_vals_1122_, v_i_1123_);
if (lean_obj_tag(v_k_1127_) == 0)
{
uint64_t v___x_1141_; 
v___x_1141_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1130_ = v___x_1141_;
goto v___jp_1129_;
}
else
{
uint64_t v_hash_1142_; 
v_hash_1142_ = lean_ctor_get_uint64(v_k_1127_, sizeof(void*)*2);
v___y_1130_ = v_hash_1142_;
goto v___jp_1129_;
}
v___jp_1129_:
{
size_t v_h_1131_; size_t v___x_1132_; lean_object* v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; size_t v_h_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_h_1131_ = lean_uint64_to_usize(v___y_1130_);
v___x_1132_ = ((size_t)5ULL);
v___x_1133_ = lean_unsigned_to_nat(1u);
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_sub(v_depth_1120_, v___x_1134_);
v___x_1136_ = lean_usize_mul(v___x_1132_, v___x_1135_);
v_h_1137_ = lean_usize_shift_right(v_h_1131_, v___x_1136_);
v___x_1138_ = lean_nat_add(v_i_1123_, v___x_1133_);
lean_dec(v_i_1123_);
lean_inc(v_v_1128_);
lean_inc(v_k_1127_);
v___x_1139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1124_, v_h_1137_, v_depth_1120_, v_k_1127_, v_v_1128_);
v_i_1123_ = v___x_1138_;
v_entries_1124_ = v___x_1139_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1143_, lean_object* v_keys_1144_, lean_object* v_vals_1145_, lean_object* v_i_1146_, lean_object* v_entries_1147_){
_start:
{
size_t v_depth_boxed_1148_; lean_object* v_res_1149_; 
v_depth_boxed_1148_ = lean_unbox_usize(v_depth_1143_);
lean_dec(v_depth_1143_);
v_res_1149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1148_, v_keys_1144_, v_vals_1145_, v_i_1146_, v_entries_1147_);
lean_dec_ref(v_vals_1145_);
lean_dec_ref(v_keys_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
size_t v_x_634__boxed_1155_; size_t v_x_635__boxed_1156_; lean_object* v_res_1157_; 
v_x_634__boxed_1155_ = lean_unbox_usize(v_x_1151_);
lean_dec(v_x_1151_);
v_x_635__boxed_1156_ = lean_unbox_usize(v_x_1152_);
lean_dec(v_x_1152_);
v_res_1157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1150_, v_x_634__boxed_1155_, v_x_635__boxed_1156_, v_x_1153_, v_x_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
uint64_t v___y_1162_; 
if (lean_obj_tag(v_x_1159_) == 0)
{
uint64_t v___x_1166_; 
v___x_1166_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1162_ = v___x_1166_;
goto v___jp_1161_;
}
else
{
uint64_t v_hash_1167_; 
v_hash_1167_ = lean_ctor_get_uint64(v_x_1159_, sizeof(void*)*2);
v___y_1162_ = v_hash_1167_;
goto v___jp_1161_;
}
v___jp_1161_:
{
size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_uint64_to_usize(v___y_1162_);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1158_, v___x_1163_, v___x_1164_, v_x_1159_, v_x_1160_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1168_, lean_object* v_as_1169_, size_t v_i_1170_, size_t v_stop_1171_, lean_object* v_b_1172_){
_start:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_usize_dec_eq(v_i_1170_, v_stop_1171_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; 
v___x_1174_ = lean_array_uget_borrowed(v_as_1169_, v_i_1170_);
lean_inc(v_declName_1168_);
lean_inc(v___x_1174_);
v___x_1175_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1172_, v___x_1174_, v_declName_1168_);
v___x_1176_ = ((size_t)1ULL);
v___x_1177_ = lean_usize_add(v_i_1170_, v___x_1176_);
v_i_1170_ = v___x_1177_;
v_b_1172_ = v___x_1175_;
goto _start;
}
else
{
lean_dec(v_declName_1168_);
return v_b_1172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1179_, lean_object* v_as_1180_, lean_object* v_i_1181_, lean_object* v_stop_1182_, lean_object* v_b_1183_){
_start:
{
size_t v_i_boxed_1184_; size_t v_stop_boxed_1185_; lean_object* v_res_1186_; 
v_i_boxed_1184_ = lean_unbox_usize(v_i_1181_);
lean_dec(v_i_1181_);
v_stop_boxed_1185_ = lean_unbox_usize(v_stop_1182_);
lean_dec(v_stop_1182_);
v_res_1186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1179_, v_as_1180_, v_i_boxed_1184_, v_stop_boxed_1185_, v_b_1183_);
lean_dec_ref(v_as_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1187_, lean_object* v_declName_1188_, lean_object* v_s_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_array_get_size(v_eqThms_1187_);
v___x_1192_ = lean_nat_dec_lt(v___x_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_dec(v_declName_1188_);
return v_s_1189_;
}
else
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_nat_dec_le(v___x_1191_, v___x_1191_);
if (v___x_1193_ == 0)
{
if (v___x_1192_ == 0)
{
lean_dec(v_declName_1188_);
return v_s_1189_;
}
else
{
size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((size_t)0ULL);
v___x_1195_ = lean_usize_of_nat(v___x_1191_);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1188_, v_eqThms_1187_, v___x_1194_, v___x_1195_, v_s_1189_);
return v___x_1196_;
}
}
else
{
size_t v___x_1197_; size_t v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = ((size_t)0ULL);
v___x_1198_ = lean_usize_of_nat(v___x_1191_);
v___x_1199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1188_, v_eqThms_1187_, v___x_1197_, v___x_1198_, v_s_1189_);
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1200_, lean_object* v_declName_1201_, lean_object* v_s_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1200_, v_declName_1201_, v_s_1202_);
lean_dec_ref(v_eqThms_1200_);
return v_res_1203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1209_, lean_object* v_eqThms_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v_env_1214_; lean_object* v_nextMacroScope_1215_; lean_object* v_ngen_1216_; lean_object* v_auxDeclNGen_1217_; lean_object* v_traceState_1218_; lean_object* v_messages_1219_; lean_object* v_infoState_1220_; lean_object* v_snapshotTasks_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1237_; 
v___x_1213_ = lean_st_ref_take(v_a_1211_);
v_env_1214_ = lean_ctor_get(v___x_1213_, 0);
v_nextMacroScope_1215_ = lean_ctor_get(v___x_1213_, 1);
v_ngen_1216_ = lean_ctor_get(v___x_1213_, 2);
v_auxDeclNGen_1217_ = lean_ctor_get(v___x_1213_, 3);
v_traceState_1218_ = lean_ctor_get(v___x_1213_, 4);
v_messages_1219_ = lean_ctor_get(v___x_1213_, 6);
v_infoState_1220_ = lean_ctor_get(v___x_1213_, 7);
v_snapshotTasks_1221_ = lean_ctor_get(v___x_1213_, 8);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1213_, 5);
lean_dec(v_unused_1238_);
v___x_1223_ = v___x_1213_;
v_isShared_1224_ = v_isSharedCheck_1237_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snapshotTasks_1221_);
lean_inc(v_infoState_1220_);
lean_inc(v_messages_1219_);
lean_inc(v_traceState_1218_);
lean_inc(v_auxDeclNGen_1217_);
lean_inc(v_ngen_1216_);
lean_inc(v_nextMacroScope_1215_);
lean_inc(v_env_1214_);
lean_dec(v___x_1213_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1237_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v_asyncMode_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1225_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1226_ = lean_ctor_get(v___x_1225_, 2);
lean_inc(v_asyncMode_1226_);
v___f_1227_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1227_, 0, v_eqThms_1210_);
lean_closure_set(v___f_1227_, 1, v_declName_1209_);
v___x_1228_ = lean_box(0);
v___x_1229_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1225_, v_env_1214_, v___f_1227_, v_asyncMode_1226_, v___x_1228_);
lean_dec(v_asyncMode_1226_);
v___x_1230_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 5, v___x_1230_);
lean_ctor_set(v___x_1223_, 0, v___x_1229_);
v___x_1232_ = v___x_1223_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_nextMacroScope_1215_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_ngen_1216_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_auxDeclNGen_1217_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_traceState_1218_);
lean_ctor_set(v_reuseFailAlloc_1236_, 5, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1236_, 6, v_messages_1219_);
lean_ctor_set(v_reuseFailAlloc_1236_, 7, v_infoState_1220_);
lean_ctor_set(v_reuseFailAlloc_1236_, 8, v_snapshotTasks_1221_);
v___x_1232_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_st_ref_set(v_a_1211_, v___x_1232_);
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1239_, lean_object* v_eqThms_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1239_, v_eqThms_1240_, v_a_1241_);
lean_dec(v_a_1241_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1244_, lean_object* v_eqThms_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1244_, v_eqThms_1245_, v_a_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1250_, lean_object* v_eqThms_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1250_, v_eqThms_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1257_, v_x_1258_, v_x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1261_, lean_object* v_x_1262_, size_t v_x_1263_, size_t v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1262_, v_x_1263_, v_x_1264_, v_x_1265_, v_x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
size_t v_x_912__boxed_1274_; size_t v_x_913__boxed_1275_; lean_object* v_res_1276_; 
v_x_912__boxed_1274_ = lean_unbox_usize(v_x_1270_);
lean_dec(v_x_1270_);
v_x_913__boxed_1275_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_res_1276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1268_, v_x_1269_, v_x_912__boxed_1274_, v_x_913__boxed_1275_, v_x_1272_, v_x_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1277_, lean_object* v_n_1278_, lean_object* v_k_1279_, lean_object* v_v_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1278_, v_k_1279_, v_v_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1282_, size_t v_depth_1283_, lean_object* v_keys_1284_, lean_object* v_vals_1285_, lean_object* v_heq_1286_, lean_object* v_i_1287_, lean_object* v_entries_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1283_, v_keys_1284_, v_vals_1285_, v_i_1287_, v_entries_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1290_, lean_object* v_depth_1291_, lean_object* v_keys_1292_, lean_object* v_vals_1293_, lean_object* v_heq_1294_, lean_object* v_i_1295_, lean_object* v_entries_1296_){
_start:
{
size_t v_depth_boxed_1297_; lean_object* v_res_1298_; 
v_depth_boxed_1297_ = lean_unbox_usize(v_depth_1291_);
lean_dec(v_depth_1291_);
v_res_1298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1290_, v_depth_boxed_1297_, v_keys_1292_, v_vals_1293_, v_heq_1294_, v_i_1295_, v_entries_1296_);
lean_dec_ref(v_vals_1293_);
lean_dec_ref(v_keys_1292_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1300_, v_x_1301_, v_x_1302_, v_x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1305_, lean_object* v_env_1306_, lean_object* v_idx_1307_, lean_object* v_eqs_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_nextEq_1315_; uint8_t v___x_1316_; 
v___x_1310_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1311_ = lean_unsigned_to_nat(1u);
v___x_1312_ = lean_nat_add(v_idx_1307_, v___x_1311_);
lean_dec(v_idx_1307_);
lean_inc(v___x_1312_);
v___x_1313_ = l_Nat_reprFast(v___x_1312_);
v___x_1314_ = lean_string_append(v___x_1310_, v___x_1313_);
lean_dec_ref(v___x_1313_);
lean_inc(v_declName_1305_);
lean_inc_ref(v_env_1306_);
v_nextEq_1315_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1306_, v_declName_1305_, v___x_1314_);
lean_inc_ref(v_env_1306_);
v___x_1316_ = l_Lean_Environment_containsOnBranch(v_env_1306_, v_nextEq_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec(v_nextEq_1315_);
lean_dec(v___x_1312_);
lean_dec_ref(v_env_1306_);
lean_dec(v_declName_1305_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_eqs_1308_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_array_push(v_eqs_1308_, v_nextEq_1315_);
v_idx_1307_ = v___x_1312_;
v_eqs_1308_ = v___x_1318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1320_, lean_object* v_env_1321_, lean_object* v_idx_1322_, lean_object* v_eqs_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1320_, v_env_1321_, v_idx_1322_, v_eqs_1323_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1326_, lean_object* v_env_1327_, lean_object* v_idx_1328_, lean_object* v_eqs_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1326_, v_env_1327_, v_idx_1328_, v_eqs_1329_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1336_, lean_object* v_env_1337_, lean_object* v_idx_1338_, lean_object* v_eqs_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1336_, v_env_1337_, v_idx_1338_, v_eqs_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v_env_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; 
v___x_1349_ = lean_st_ref_get(v_a_1347_);
v_env_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_ref(v_env_1350_);
lean_dec(v___x_1349_);
v___x_1351_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1346_);
lean_inc_ref(v_env_1350_);
v___x_1352_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1350_, v_declName_1346_, v___x_1351_);
v___x_1353_ = 1;
lean_inc(v___x_1352_);
lean_inc_ref(v_env_1350_);
v___x_1354_ = l_Lean_Environment_contains(v_env_1350_, v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v___x_1352_);
lean_dec_ref(v_env_1350_);
lean_dec(v_declName_1346_);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_mk_empty_array_with_capacity(v___x_1357_);
v___x_1359_ = lean_array_push(v___x_1358_, v___x_1352_);
lean_inc(v_declName_1346_);
v___x_1360_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1346_, v_env_1350_, v___x_1357_, v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
lean_inc(v_a_1361_);
v___x_1362_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1346_, v_a_1361_, v_a_1347_);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v___x_1362_, 0);
lean_dec(v_unused_1371_);
v___x_1364_ = v___x_1362_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v___x_1362_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1361_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_declName_1346_);
v_a_1372_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1360_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1360_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1380_, v_a_1381_);
lean_dec(v_a_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1384_, v_a_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1398_, lean_object* v_localInsts_1399_, lean_object* v_x_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1398_, v_localInsts_1399_, v_x_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
v_a_1415_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1406_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1406_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1423_, lean_object* v_localInsts_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1423_, v_localInsts_1424_, v_x_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1432_, lean_object* v_lctx_1433_, lean_object* v_localInsts_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1433_, v_localInsts_1434_, v_x_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1442_, lean_object* v_lctx_1443_, lean_object* v_localInsts_1444_, lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1442_, v_lctx_1443_, v_localInsts_1444_, v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1455_, lean_object* v_as_x27_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
if (lean_obj_tag(v_as_x27_1456_) == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_declName_1455_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1457_);
return v___x_1463_;
}
else
{
lean_object* v_head_1464_; lean_object* v_tail_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v_b_1457_);
v_head_1464_ = lean_ctor_get(v_as_x27_1456_, 0);
v_tail_1465_ = lean_ctor_get(v_as_x27_1456_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_as_x27_1456_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1467_ = v_as_x27_1456_;
v_isShared_1468_ = v_isSharedCheck_1496_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_tail_1465_);
lean_inc(v_head_1464_);
lean_dec(v_as_x27_1456_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1496_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; 
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v_declName_1455_);
v___x_1469_ = lean_apply_6(v_head_1464_, v_declName_1455_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, lean_box(0));
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___x_1469_);
v___x_1471_ = lean_box(0);
if (lean_obj_tag(v_a_1470_) == 1)
{
lean_object* v_val_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_tail_1465_);
v_val_1472_ = lean_ctor_get(v_a_1470_, 0);
lean_inc(v_val_1472_);
v___x_1473_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1455_, v_val_1472_, v___y_1461_);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v___x_1473_, 0);
lean_dec(v_unused_1485_);
v___x_1475_ = v___x_1473_;
v_isShared_1476_ = v_isSharedCheck_1484_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v___x_1473_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1484_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_a_1470_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 0);
lean_ctor_set(v___x_1467_, 1, v___x_1471_);
lean_ctor_set(v___x_1467_, 0, v___x_1477_);
v___x_1479_ = v___x_1467_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___x_1471_);
v___x_1479_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1479_);
v___x_1481_ = v___x_1475_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_a_1470_);
lean_del_object(v___x_1467_);
v___x_1486_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1456_ = v_tail_1465_;
v_b_1457_ = v___x_1486_;
goto _start;
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_del_object(v___x_1467_);
lean_dec(v_tail_1465_);
lean_dec(v_declName_1455_);
v_a_1488_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1469_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1469_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1497_, lean_object* v_as_x27_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1497_, v_as_x27_1498_, v_b_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
lean_inc(v_declName_1506_);
v___x_1512_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1550_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1550_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1550_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_unbox(v_a_1513_);
lean_dec(v_a_1513_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
lean_dec(v_declName_1506_);
v___x_1518_ = lean_box(0);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1518_);
v___x_1520_ = v___x_1515_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
else
{
lean_object* v___x_1522_; 
lean_del_object(v___x_1515_);
lean_inc(v_declName_1506_);
v___x_1522_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1506_, v___y_1510_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
if (lean_obj_tag(v_a_1523_) == 1)
{
lean_dec_ref(v_a_1523_);
lean_dec(v_declName_1506_);
return v___x_1522_;
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_a_1523_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1525_ = lean_st_ref_get(v___x_1524_);
v___x_1526_ = lean_box(0);
v___x_1527_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1528_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1506_, v___x_1525_, v___x_1527_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1541_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1541_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1541_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_fst_1533_; 
v_fst_1533_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_fst_1533_);
lean_dec(v_a_1529_);
if (lean_obj_tag(v_fst_1533_) == 0)
{
lean_object* v___x_1535_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1526_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1526_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
lean_object* v_val_1537_; lean_object* v___x_1539_; 
v_val_1537_ = lean_ctor_get(v_fst_1533_, 0);
lean_inc(v_val_1537_);
lean_dec_ref(v_fst_1533_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v_val_1537_);
v___x_1539_ = v___x_1531_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_val_1537_);
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
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1528_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1528_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
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
}
}
else
{
lean_dec(v_declName_1506_);
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_declName_1506_);
v_a_1551_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1512_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1512_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
return v_res_1565_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = lean_box(1);
v___x_1570_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1571_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1570_);
lean_ctor_set(v___x_1572_, 2, v___x_1569_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___f_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___f_1581_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1581_, 0, v_declName_1575_);
v___x_1582_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1583_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1584_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1582_, v___x_1583_, v___f_1581_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1592_, lean_object* v_as_1593_, lean_object* v_as_x27_1594_, lean_object* v_b_1595_, lean_object* v_a_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1592_, v_as_x27_1594_, v_b_1595_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1603_, lean_object* v_as_1604_, lean_object* v_as_x27_1605_, lean_object* v_b_1606_, lean_object* v_a_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1603_, v_as_1604_, v_as_x27_1605_, v_b_1606_, v_a_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v_as_1604_);
return v_res_1613_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(lean_object* v_opts_1614_, lean_object* v_opt_1615_){
_start:
{
lean_object* v_name_1616_; lean_object* v_defValue_1617_; lean_object* v_map_1618_; lean_object* v___x_1619_; 
v_name_1616_ = lean_ctor_get(v_opt_1615_, 0);
v_defValue_1617_ = lean_ctor_get(v_opt_1615_, 1);
v_map_1618_ = lean_ctor_get(v_opts_1614_, 0);
v___x_1619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1618_, v_name_1616_);
if (lean_obj_tag(v___x_1619_) == 0)
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_unbox(v_defValue_1617_);
return v___x_1620_;
}
else
{
lean_object* v_val_1621_; 
v_val_1621_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_val_1621_);
lean_dec_ref(v___x_1619_);
if (lean_obj_tag(v_val_1621_) == 1)
{
uint8_t v_v_1622_; 
v_v_1622_ = lean_ctor_get_uint8(v_val_1621_, 0);
lean_dec_ref(v_val_1621_);
return v_v_1622_;
}
else
{
uint8_t v___x_1623_; 
lean_dec(v_val_1621_);
v___x_1623_ = lean_unbox(v_defValue_1617_);
return v___x_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1___boxed(lean_object* v_opts_1624_, lean_object* v_opt_1625_){
_start:
{
uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_res_1626_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_1624_, v_opt_1625_);
lean_dec_ref(v_opt_1625_);
lean_dec_ref(v_opts_1624_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(lean_object* v_opts_1628_, lean_object* v_opt_1629_){
_start:
{
lean_object* v_name_1630_; lean_object* v_defValue_1631_; lean_object* v_map_1632_; lean_object* v___x_1633_; 
v_name_1630_ = lean_ctor_get(v_opt_1629_, 0);
v_defValue_1631_ = lean_ctor_get(v_opt_1629_, 1);
v_map_1632_ = lean_ctor_get(v_opts_1628_, 0);
v___x_1633_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1632_, v_name_1630_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_inc(v_defValue_1631_);
return v_defValue_1631_;
}
else
{
lean_object* v_val_1634_; 
v_val_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_val_1634_);
lean_dec_ref(v___x_1633_);
if (lean_obj_tag(v_val_1634_) == 3)
{
lean_object* v_v_1635_; 
v_v_1635_ = lean_ctor_get(v_val_1634_, 0);
lean_inc(v_v_1635_);
lean_dec_ref(v_val_1634_);
return v_v_1635_;
}
else
{
lean_dec(v_val_1634_);
lean_inc(v_defValue_1631_);
return v_defValue_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2___boxed(lean_object* v_opts_1636_, lean_object* v_opt_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_1636_, v_opt_1637_);
lean_dec_ref(v_opt_1637_);
lean_dec_ref(v_opts_1636_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(lean_object* v_o_1642_, lean_object* v_k_1643_, uint8_t v_v_1644_){
_start:
{
lean_object* v_map_1645_; uint8_t v_hasTrace_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1660_; 
v_map_1645_ = lean_ctor_get(v_o_1642_, 0);
v_hasTrace_1646_ = lean_ctor_get_uint8(v_o_1642_, sizeof(void*)*1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_o_1642_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1648_ = v_o_1642_;
v_isShared_1649_ = v_isSharedCheck_1660_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_map_1645_);
lean_dec(v_o_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1660_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1650_, 0, v_v_1644_);
lean_inc(v_k_1643_);
v___x_1651_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1643_, v___x_1650_, v_map_1645_);
if (v_hasTrace_1646_ == 0)
{
lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1655_; 
v___x_1652_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1653_ = l_Lean_Name_isPrefixOf(v___x_1652_, v_k_1643_);
lean_dec(v_k_1643_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1651_);
v___x_1655_ = v___x_1648_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1651_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*1, v___x_1653_);
return v___x_1655_;
}
}
else
{
lean_object* v___x_1658_; 
lean_dec(v_k_1643_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1651_);
v___x_1658_ = v___x_1648_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1659_, sizeof(void*)*1, v_hasTrace_1646_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___boxed(lean_object* v_o_1661_, lean_object* v_k_1662_, lean_object* v_v_1663_){
_start:
{
uint8_t v_v_boxed_1664_; lean_object* v_res_1665_; 
v_v_boxed_1664_ = lean_unbox(v_v_1663_);
v_res_1665_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_o_1661_, v_k_1662_, v_v_boxed_1664_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(lean_object* v_opts_1666_, lean_object* v_opt_1667_, uint8_t v_val_1668_){
_start:
{
lean_object* v_name_1669_; lean_object* v___x_1670_; 
v_name_1669_ = lean_ctor_get(v_opt_1667_, 0);
lean_inc(v_name_1669_);
lean_dec_ref(v_opt_1667_);
v___x_1670_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_opts_1666_, v_name_1669_, v_val_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object* v_opts_1671_, lean_object* v_opt_1672_, lean_object* v_val_1673_){
_start:
{
uint8_t v_val_boxed_1674_; lean_object* v_res_1675_; 
v_val_boxed_1674_ = lean_unbox(v_val_1673_);
v_res_1675_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_opts_1671_, v_opt_1672_, v_val_boxed_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(lean_object* v_as_1676_, size_t v_i_1677_, size_t v_stop_1678_, lean_object* v_b_1679_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_eq(v_i_1677_, v_stop_1678_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v_defValue_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; 
v___x_1681_ = lean_array_uget_borrowed(v_as_1676_, v_i_1677_);
v_defValue_1682_ = lean_ctor_get(v___x_1681_, 1);
v___x_1683_ = lean_unbox(v_defValue_1682_);
lean_inc(v___x_1681_);
v___x_1684_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_b_1679_, v___x_1681_, v___x_1683_);
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1677_, v___x_1685_);
v_i_1677_ = v___x_1686_;
v_b_1679_ = v___x_1684_;
goto _start;
}
else
{
return v_b_1679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3___boxed(lean_object* v_as_1688_, lean_object* v_i_1689_, lean_object* v_stop_1690_, lean_object* v_b_1691_){
_start:
{
size_t v_i_boxed_1692_; size_t v_stop_boxed_1693_; lean_object* v_res_1694_; 
v_i_boxed_1692_ = lean_unbox_usize(v_i_1689_);
lean_dec(v_i_1689_);
v_stop_boxed_1693_ = lean_unbox_usize(v_stop_1690_);
lean_dec(v_stop_1690_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v_as_1688_, v_i_boxed_1692_, v_stop_boxed_1693_, v_b_1691_);
lean_dec_ref(v_as_1688_);
return v_res_1694_;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1696_ = lean_array_get_size(v___x_1695_);
return v___x_1696_;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1698_ = lean_nat_dec_le(v___x_1697_, v___x_1697_);
return v___x_1698_;
}
}
static size_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1699_; size_t v___x_1700_; 
v___x_1699_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1700_ = lean_usize_of_nat(v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object* v_declName_1701_, lean_object* v___x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v_fileName_1711_; lean_object* v_fileMap_1712_; lean_object* v_currRecDepth_1713_; lean_object* v_ref_1714_; lean_object* v_currNamespace_1715_; lean_object* v_openDecls_1716_; lean_object* v_initHeartbeats_1717_; lean_object* v_maxHeartbeats_1718_; lean_object* v_quotContext_1719_; lean_object* v_currMacroScope_1720_; lean_object* v_cancelTk_x3f_1721_; uint8_t v_suppressElabErrors_1722_; lean_object* v_inheritedTraceOptions_1723_; lean_object* v___y_1724_; lean_object* v___x_1729_; lean_object* v_fileName_1730_; lean_object* v_fileMap_1731_; lean_object* v_options_1732_; lean_object* v_currRecDepth_1733_; lean_object* v_ref_1734_; lean_object* v_currNamespace_1735_; lean_object* v_openDecls_1736_; lean_object* v_initHeartbeats_1737_; lean_object* v_maxHeartbeats_1738_; lean_object* v_quotContext_1739_; lean_object* v_currMacroScope_1740_; lean_object* v_cancelTk_x3f_1741_; uint8_t v_suppressElabErrors_1742_; lean_object* v_inheritedTraceOptions_1743_; uint8_t v___y_1745_; lean_object* v___y_1746_; uint8_t v___y_1747_; lean_object* v___y_1769_; lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1729_ = lean_st_ref_get(v___y_1706_);
v_fileName_1730_ = lean_ctor_get(v___y_1705_, 0);
lean_inc_ref(v_fileName_1730_);
v_fileMap_1731_ = lean_ctor_get(v___y_1705_, 1);
lean_inc_ref(v_fileMap_1731_);
v_options_1732_ = lean_ctor_get(v___y_1705_, 2);
lean_inc_ref(v_options_1732_);
v_currRecDepth_1733_ = lean_ctor_get(v___y_1705_, 3);
lean_inc(v_currRecDepth_1733_);
v_ref_1734_ = lean_ctor_get(v___y_1705_, 5);
lean_inc(v_ref_1734_);
v_currNamespace_1735_ = lean_ctor_get(v___y_1705_, 6);
lean_inc(v_currNamespace_1735_);
v_openDecls_1736_ = lean_ctor_get(v___y_1705_, 7);
lean_inc(v_openDecls_1736_);
v_initHeartbeats_1737_ = lean_ctor_get(v___y_1705_, 8);
lean_inc(v_initHeartbeats_1737_);
v_maxHeartbeats_1738_ = lean_ctor_get(v___y_1705_, 9);
lean_inc(v_maxHeartbeats_1738_);
v_quotContext_1739_ = lean_ctor_get(v___y_1705_, 10);
lean_inc(v_quotContext_1739_);
v_currMacroScope_1740_ = lean_ctor_get(v___y_1705_, 11);
lean_inc(v_currMacroScope_1740_);
v_cancelTk_x3f_1741_ = lean_ctor_get(v___y_1705_, 12);
lean_inc(v_cancelTk_x3f_1741_);
v_suppressElabErrors_1742_ = lean_ctor_get_uint8(v___y_1705_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1743_ = lean_ctor_get(v___y_1705_, 13);
lean_inc_ref(v_inheritedTraceOptions_1743_);
lean_dec_ref(v___y_1705_);
v___x_1774_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1775_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1776_ = lean_nat_dec_lt(v___x_1702_, v___x_1775_);
if (v___x_1776_ == 0)
{
v___y_1769_ = v_options_1732_;
goto v___jp_1768_;
}
else
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_uint8_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1);
if (v___x_1777_ == 0)
{
if (v___x_1776_ == 0)
{
v___y_1769_ = v_options_1732_;
goto v___jp_1768_;
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1774_, v___x_1778_, v___x_1779_, v_options_1732_);
v___y_1769_ = v___x_1780_;
goto v___jp_1768_;
}
}
else
{
size_t v___x_1781_; size_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1774_, v___x_1781_, v___x_1782_, v_options_1732_);
v___y_1769_ = v___x_1783_;
goto v___jp_1768_;
}
}
v___jp_1708_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1725_ = l_Lean_maxRecDepth;
v___x_1726_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v___y_1710_, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1727_, 0, v_fileName_1711_);
lean_ctor_set(v___x_1727_, 1, v_fileMap_1712_);
lean_ctor_set(v___x_1727_, 2, v___y_1710_);
lean_ctor_set(v___x_1727_, 3, v_currRecDepth_1713_);
lean_ctor_set(v___x_1727_, 4, v___x_1726_);
lean_ctor_set(v___x_1727_, 5, v_ref_1714_);
lean_ctor_set(v___x_1727_, 6, v_currNamespace_1715_);
lean_ctor_set(v___x_1727_, 7, v_openDecls_1716_);
lean_ctor_set(v___x_1727_, 8, v_initHeartbeats_1717_);
lean_ctor_set(v___x_1727_, 9, v_maxHeartbeats_1718_);
lean_ctor_set(v___x_1727_, 10, v_quotContext_1719_);
lean_ctor_set(v___x_1727_, 11, v_currMacroScope_1720_);
lean_ctor_set(v___x_1727_, 12, v_cancelTk_x3f_1721_);
lean_ctor_set(v___x_1727_, 13, v_inheritedTraceOptions_1723_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*14, v___y_1709_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*14 + 1, v_suppressElabErrors_1722_);
v___x_1728_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1701_, v___y_1703_, v___y_1704_, v___x_1727_, v___y_1724_);
lean_dec_ref(v___x_1727_);
return v___x_1728_;
}
v___jp_1744_:
{
if (v___y_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v_env_1749_; lean_object* v_nextMacroScope_1750_; lean_object* v_ngen_1751_; lean_object* v_auxDeclNGen_1752_; lean_object* v_traceState_1753_; lean_object* v_messages_1754_; lean_object* v_infoState_1755_; lean_object* v_snapshotTasks_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1766_; 
v___x_1748_ = lean_st_ref_take(v___y_1706_);
v_env_1749_ = lean_ctor_get(v___x_1748_, 0);
v_nextMacroScope_1750_ = lean_ctor_get(v___x_1748_, 1);
v_ngen_1751_ = lean_ctor_get(v___x_1748_, 2);
v_auxDeclNGen_1752_ = lean_ctor_get(v___x_1748_, 3);
v_traceState_1753_ = lean_ctor_get(v___x_1748_, 4);
v_messages_1754_ = lean_ctor_get(v___x_1748_, 6);
v_infoState_1755_ = lean_ctor_get(v___x_1748_, 7);
v_snapshotTasks_1756_ = lean_ctor_get(v___x_1748_, 8);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v___x_1748_, 5);
lean_dec(v_unused_1767_);
v___x_1758_ = v___x_1748_;
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_snapshotTasks_1756_);
lean_inc(v_infoState_1755_);
lean_inc(v_messages_1754_);
lean_inc(v_traceState_1753_);
lean_inc(v_auxDeclNGen_1752_);
lean_inc(v_ngen_1751_);
lean_inc(v_nextMacroScope_1750_);
lean_inc(v_env_1749_);
lean_dec(v___x_1748_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1760_ = l_Lean_Kernel_enableDiag(v_env_1749_, v___y_1745_);
v___x_1761_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 5, v___x_1761_);
lean_ctor_set(v___x_1758_, 0, v___x_1760_);
v___x_1763_ = v___x_1758_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_nextMacroScope_1750_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_ngen_1751_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_auxDeclNGen_1752_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_traceState_1753_);
lean_ctor_set(v_reuseFailAlloc_1765_, 5, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1765_, 6, v_messages_1754_);
lean_ctor_set(v_reuseFailAlloc_1765_, 7, v_infoState_1755_);
lean_ctor_set(v_reuseFailAlloc_1765_, 8, v_snapshotTasks_1756_);
v___x_1763_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_st_ref_set(v___y_1706_, v___x_1763_);
v___y_1709_ = v___y_1745_;
v___y_1710_ = v___y_1746_;
v_fileName_1711_ = v_fileName_1730_;
v_fileMap_1712_ = v_fileMap_1731_;
v_currRecDepth_1713_ = v_currRecDepth_1733_;
v_ref_1714_ = v_ref_1734_;
v_currNamespace_1715_ = v_currNamespace_1735_;
v_openDecls_1716_ = v_openDecls_1736_;
v_initHeartbeats_1717_ = v_initHeartbeats_1737_;
v_maxHeartbeats_1718_ = v_maxHeartbeats_1738_;
v_quotContext_1719_ = v_quotContext_1739_;
v_currMacroScope_1720_ = v_currMacroScope_1740_;
v_cancelTk_x3f_1721_ = v_cancelTk_x3f_1741_;
v_suppressElabErrors_1722_ = v_suppressElabErrors_1742_;
v_inheritedTraceOptions_1723_ = v_inheritedTraceOptions_1743_;
v___y_1724_ = v___y_1706_;
goto v___jp_1708_;
}
}
}
else
{
v___y_1709_ = v___y_1745_;
v___y_1710_ = v___y_1746_;
v_fileName_1711_ = v_fileName_1730_;
v_fileMap_1712_ = v_fileMap_1731_;
v_currRecDepth_1713_ = v_currRecDepth_1733_;
v_ref_1714_ = v_ref_1734_;
v_currNamespace_1715_ = v_currNamespace_1735_;
v_openDecls_1716_ = v_openDecls_1736_;
v_initHeartbeats_1717_ = v_initHeartbeats_1737_;
v_maxHeartbeats_1718_ = v_maxHeartbeats_1738_;
v_quotContext_1719_ = v_quotContext_1739_;
v_currMacroScope_1720_ = v_currMacroScope_1740_;
v_cancelTk_x3f_1721_ = v_cancelTk_x3f_1741_;
v_suppressElabErrors_1722_ = v_suppressElabErrors_1742_;
v_inheritedTraceOptions_1723_ = v_inheritedTraceOptions_1743_;
v___y_1724_ = v___y_1706_;
goto v___jp_1708_;
}
}
v___jp_1768_:
{
lean_object* v_env_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; uint8_t v___x_1773_; 
v_env_1770_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref(v_env_1770_);
lean_dec(v___x_1729_);
v___x_1771_ = l_Lean_diagnostics;
v___x_1772_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___y_1769_, v___x_1771_);
v___x_1773_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1770_);
lean_dec_ref(v_env_1770_);
if (v___x_1773_ == 0)
{
if (v___x_1772_ == 0)
{
v___y_1709_ = v___x_1772_;
v___y_1710_ = v___y_1769_;
v_fileName_1711_ = v_fileName_1730_;
v_fileMap_1712_ = v_fileMap_1731_;
v_currRecDepth_1713_ = v_currRecDepth_1733_;
v_ref_1714_ = v_ref_1734_;
v_currNamespace_1715_ = v_currNamespace_1735_;
v_openDecls_1716_ = v_openDecls_1736_;
v_initHeartbeats_1717_ = v_initHeartbeats_1737_;
v_maxHeartbeats_1718_ = v_maxHeartbeats_1738_;
v_quotContext_1719_ = v_quotContext_1739_;
v_currMacroScope_1720_ = v_currMacroScope_1740_;
v_cancelTk_x3f_1721_ = v_cancelTk_x3f_1741_;
v_suppressElabErrors_1722_ = v_suppressElabErrors_1742_;
v_inheritedTraceOptions_1723_ = v_inheritedTraceOptions_1743_;
v___y_1724_ = v___y_1706_;
goto v___jp_1708_;
}
else
{
v___y_1745_ = v___x_1772_;
v___y_1746_ = v___y_1769_;
v___y_1747_ = v___x_1773_;
goto v___jp_1744_;
}
}
else
{
v___y_1745_ = v___x_1772_;
v___y_1746_ = v___y_1769_;
v___y_1747_ = v___x_1772_;
goto v___jp_1744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object* v_declName_1784_, lean_object* v___x_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_Meta_getEqnsFor_x3f___lam__0(v_declName_1784_, v___x_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___x_1785_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___f_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1798_ = lean_unsigned_to_nat(32u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
lean_dec_ref(v___x_1799_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___f_1801_ = lean_alloc_closure((void*)(l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1801_, 0, v_declName_1792_);
lean_closure_set(v___f_1801_, 1, v___x_1800_);
v___x_1802_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1803_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1804_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1802_, v___x_1803_, v___f_1801_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(lean_object* v_cls_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_options_1815_; uint8_t v_hasTrace_1816_; 
v_options_1815_ = lean_ctor_get(v___y_1813_, 2);
v_hasTrace_1816_ = lean_ctor_get_uint8(v_options_1815_, sizeof(void*)*1);
if (v_hasTrace_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v_cls_1812_);
v___x_1817_ = lean_box(v_hasTrace_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
else
{
lean_object* v_inheritedTraceOptions_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_inheritedTraceOptions_1819_ = lean_ctor_get(v___y_1813_, 13);
v___x_1820_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1821_ = l_Lean_Name_append(v___x_1820_, v_cls_1812_);
v___x_1822_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1819_, v_options_1815_, v___x_1821_);
lean_dec(v___x_1821_);
v___x_1823_ = lean_box(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg___boxed(lean_object* v_cls_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v_cls_1825_, v___y_1826_);
lean_dec_ref(v___y_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1(lean_object* v_cls_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v_cls_1829_, v___y_1832_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___boxed(lean_object* v_cls_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1(v_cls_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(lean_object* v_msgData_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v_env_1850_; lean_object* v___x_1851_; lean_object* v_mctx_1852_; lean_object* v_lctx_1853_; lean_object* v_options_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1849_ = lean_st_ref_get(v___y_1847_);
v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref(v_env_1850_);
lean_dec(v___x_1849_);
v___x_1851_ = lean_st_ref_get(v___y_1845_);
v_mctx_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc_ref(v_mctx_1852_);
lean_dec(v___x_1851_);
v_lctx_1853_ = lean_ctor_get(v___y_1844_, 2);
v_options_1854_ = lean_ctor_get(v___y_1846_, 2);
lean_inc_ref(v_options_1854_);
lean_inc_ref(v_lctx_1853_);
v___x_1855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1855_, 0, v_env_1850_);
lean_ctor_set(v___x_1855_, 1, v_mctx_1852_);
lean_ctor_set(v___x_1855_, 2, v_lctx_1853_);
lean_ctor_set(v___x_1855_, 3, v_options_1854_);
v___x_1856_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v_msgData_1843_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2___boxed(lean_object* v_msgData_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msgData_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1864_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1865_; double v___x_1866_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_float_of_nat(v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(lean_object* v_cls_1870_, lean_object* v_msg_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_ref_1877_; lean_object* v___x_1878_; lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1923_; 
v_ref_1877_ = lean_ctor_get(v___y_1874_, 5);
v___x_1878_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msg_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1923_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1923_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v_traceState_1884_; lean_object* v_env_1885_; lean_object* v_nextMacroScope_1886_; lean_object* v_ngen_1887_; lean_object* v_auxDeclNGen_1888_; lean_object* v_cache_1889_; lean_object* v_messages_1890_; lean_object* v_infoState_1891_; lean_object* v_snapshotTasks_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1922_; 
v___x_1883_ = lean_st_ref_take(v___y_1875_);
v_traceState_1884_ = lean_ctor_get(v___x_1883_, 4);
v_env_1885_ = lean_ctor_get(v___x_1883_, 0);
v_nextMacroScope_1886_ = lean_ctor_get(v___x_1883_, 1);
v_ngen_1887_ = lean_ctor_get(v___x_1883_, 2);
v_auxDeclNGen_1888_ = lean_ctor_get(v___x_1883_, 3);
v_cache_1889_ = lean_ctor_get(v___x_1883_, 5);
v_messages_1890_ = lean_ctor_get(v___x_1883_, 6);
v_infoState_1891_ = lean_ctor_get(v___x_1883_, 7);
v_snapshotTasks_1892_ = lean_ctor_get(v___x_1883_, 8);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1894_ = v___x_1883_;
v_isShared_1895_ = v_isSharedCheck_1922_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snapshotTasks_1892_);
lean_inc(v_infoState_1891_);
lean_inc(v_messages_1890_);
lean_inc(v_cache_1889_);
lean_inc(v_traceState_1884_);
lean_inc(v_auxDeclNGen_1888_);
lean_inc(v_ngen_1887_);
lean_inc(v_nextMacroScope_1886_);
lean_inc(v_env_1885_);
lean_dec(v___x_1883_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1922_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
uint64_t v_tid_1896_; lean_object* v_traces_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1921_; 
v_tid_1896_ = lean_ctor_get_uint64(v_traceState_1884_, sizeof(void*)*1);
v_traces_1897_ = lean_ctor_get(v_traceState_1884_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_traceState_1884_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1899_ = v_traceState_1884_;
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_traces_1897_);
lean_dec(v_traceState_1884_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; double v___x_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0);
v___x_1903_ = 0;
v___x_1904_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1));
v___x_1905_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1905_, 0, v_cls_1870_);
lean_ctor_set(v___x_1905_, 1, v___x_1901_);
lean_ctor_set(v___x_1905_, 2, v___x_1904_);
lean_ctor_set_float(v___x_1905_, sizeof(void*)*3, v___x_1902_);
lean_ctor_set_float(v___x_1905_, sizeof(void*)*3 + 8, v___x_1902_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*3 + 16, v___x_1903_);
v___x_1906_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__2));
v___x_1907_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v_a_1879_);
lean_ctor_set(v___x_1907_, 2, v___x_1906_);
lean_inc(v_ref_1877_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v_ref_1877_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l_Lean_PersistentArray_push___redArg(v_traces_1897_, v___x_1908_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1909_);
v___x_1911_ = v___x_1899_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1909_);
lean_ctor_set_uint64(v_reuseFailAlloc_1920_, sizeof(void*)*1, v_tid_1896_);
v___x_1911_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 4, v___x_1911_);
v___x_1913_ = v___x_1894_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_env_1885_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_nextMacroScope_1886_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_ngen_1887_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_auxDeclNGen_1888_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1919_, 5, v_cache_1889_);
lean_ctor_set(v_reuseFailAlloc_1919_, 6, v_messages_1890_);
lean_ctor_set(v_reuseFailAlloc_1919_, 7, v_infoState_1891_);
lean_ctor_set(v_reuseFailAlloc_1919_, 8, v_snapshotTasks_1892_);
v___x_1913_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1914_ = lean_st_ref_set(v___y_1875_, v___x_1913_);
v___x_1915_ = lean_box(0);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1915_);
v___x_1917_ = v___x_1881_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___boxed(lean_object* v_cls_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(v_cls_1924_, v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(lean_object* v___x_1932_, lean_object* v_as_1933_, size_t v_i_1934_, size_t v_stop_1935_){
_start:
{
uint8_t v___x_1936_; 
v___x_1936_ = lean_usize_dec_eq(v_i_1934_, v_stop_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v_defValue_1938_; uint8_t v___x_1939_; uint8_t v___y_1945_; uint8_t v___x_1946_; 
v___x_1937_ = lean_array_uget_borrowed(v_as_1933_, v_i_1934_);
v_defValue_1938_ = lean_ctor_get(v___x_1937_, 1);
v___x_1939_ = 1;
v___x_1946_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___x_1932_, v___x_1937_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_unbox(v_defValue_1938_);
if (v___x_1947_ == 0)
{
goto v___jp_1940_;
}
else
{
v___y_1945_ = v___x_1946_;
goto v___jp_1944_;
}
}
else
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_unbox(v_defValue_1938_);
v___y_1945_ = v___x_1948_;
goto v___jp_1944_;
}
v___jp_1940_:
{
if (v___x_1936_ == 0)
{
size_t v___x_1941_; size_t v___x_1942_; 
v___x_1941_ = ((size_t)1ULL);
v___x_1942_ = lean_usize_add(v_i_1934_, v___x_1941_);
v_i_1934_ = v___x_1942_;
goto _start;
}
else
{
return v___x_1939_;
}
}
v___jp_1944_:
{
if (v___y_1945_ == 0)
{
return v___x_1939_;
}
else
{
goto v___jp_1940_;
}
}
}
else
{
uint8_t v___x_1949_; 
v___x_1949_ = 0;
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object* v___x_1950_, lean_object* v_as_1951_, lean_object* v_i_1952_, lean_object* v_stop_1953_){
_start:
{
size_t v_i_boxed_1954_; size_t v_stop_boxed_1955_; uint8_t v_res_1956_; lean_object* v_r_1957_; 
v_i_boxed_1954_ = lean_unbox_usize(v_i_1952_);
lean_dec(v_i_1952_);
v_stop_boxed_1955_ = lean_unbox_usize(v_stop_1953_);
lean_dec(v_stop_1953_);
v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v___x_1950_, v_as_1951_, v_i_boxed_1954_, v_stop_boxed_1955_);
lean_dec_ref(v_as_1951_);
lean_dec_ref(v___x_1950_);
v_r_1957_ = lean_box(v_res_1956_);
return v_r_1957_;
}
}
static uint8_t _init_l_Lean_Meta_generateEagerEqns___closed__0(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_nat_dec_lt(v___x_1959_, v___x_1958_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__5(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__4));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object* v_declName_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = l_Lean_Meta_eqnAffectingOptions;
v___x_2003_ = lean_uint8_once(&l_Lean_Meta_generateEagerEqns___closed__0, &l_Lean_Meta_generateEagerEqns___closed__0_once, _init_l_Lean_Meta_generateEagerEqns___closed__0);
if (v___x_2003_ == 0)
{
lean_dec(v_declName_1970_);
goto v___jp_1976_;
}
else
{
if (v___x_2003_ == 0)
{
lean_dec(v_declName_1970_);
goto v___jp_1976_;
}
else
{
lean_object* v_options_2004_; size_t v___x_2005_; size_t v___x_2006_; uint8_t v___x_2007_; 
v_options_2004_ = lean_ctor_get(v_a_1973_, 2);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v_options_2004_, v___x_2002_, v___x_2005_, v___x_2006_);
if (v___x_2007_ == 0)
{
lean_dec(v_declName_1970_);
goto v___jp_1976_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v_a_2010_; uint8_t v___x_2011_; 
v___x_2008_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_2009_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v___x_2008_, v_a_1973_);
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = lean_unbox(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2011_ == 0)
{
v___y_1980_ = v_a_1971_;
v___y_1981_ = v_a_1972_;
v___y_1982_ = v_a_1973_;
v___y_1983_ = v_a_1974_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2012_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__5, &l_Lean_Meta_generateEagerEqns___closed__5_once, _init_l_Lean_Meta_generateEagerEqns___closed__5);
lean_inc(v_declName_1970_);
v___x_2013_ = l_Lean_MessageData_ofName(v_declName_1970_);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(v___x_2008_, v___x_2014_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_dec_ref(v___x_2015_);
v___y_1980_ = v_a_1971_;
v___y_1981_ = v_a_1972_;
v___y_1982_ = v_a_1973_;
v___y_1983_ = v_a_1974_;
goto v___jp_1979_;
}
else
{
lean_dec(v_declName_1970_);
return v___x_2015_;
}
}
}
}
}
v___jp_1976_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
v___jp_1979_:
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1970_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1992_; 
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1984_, 0);
lean_dec(v_unused_1993_);
v___x_1986_ = v___x_1984_;
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
else
{
lean_dec(v___x_1984_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = lean_box(0);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1988_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1984_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1984_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___boxed(lean_object* v_declName_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_Meta_generateEagerEqns(v_declName_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_st_mk_ref(v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2048_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2048_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2048_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
uint8_t v___x_2036_; 
v___x_2036_ = lean_unbox(v_a_2032_);
lean_dec(v_a_2032_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec_ref(v_f_2029_);
v___x_2037_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 1);
lean_ctor_set(v___x_2034_, 0, v___x_2037_);
v___x_2039_ = v___x_2034_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2041_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2042_ = lean_st_ref_take(v___x_2041_);
v___x_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_f_2029_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_st_ref_set(v___x_2041_, v___x_2043_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2044_);
v___x_2046_ = v___x_2034_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v_f_2029_);
v_a_2049_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2031_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2031_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2063_, lean_object* v_as_x27_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
if (lean_obj_tag(v_as_x27_2064_) == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_declName_2063_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_b_2065_);
return v___x_2071_;
}
else
{
lean_object* v_head_2072_; lean_object* v_tail_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2101_; 
lean_dec_ref(v_b_2065_);
v_head_2072_ = lean_ctor_get(v_as_x27_2064_, 0);
v_tail_2073_ = lean_ctor_get(v_as_x27_2064_, 1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_as_x27_2064_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2075_ = v_as_x27_2064_;
v_isShared_2076_ = v_isSharedCheck_2101_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_tail_2073_);
lean_inc(v_head_2072_);
lean_dec(v_as_x27_2064_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2101_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; 
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2066_);
lean_inc(v_declName_2063_);
v___x_2077_ = lean_apply_6(v_head_2072_, v_declName_2063_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, lean_box(0));
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2092_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2092_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2092_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_box(0);
if (lean_obj_tag(v_a_2078_) == 1)
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
lean_dec(v_tail_2073_);
lean_dec(v_declName_2063_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_a_2078_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 0);
lean_ctor_set(v___x_2075_, 1, v___x_2082_);
lean_ctor_set(v___x_2075_, 0, v___x_2083_);
v___x_2085_ = v___x_2075_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2083_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2082_);
v___x_2085_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2087_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2085_);
v___x_2087_ = v___x_2080_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_object* v___x_2090_; 
lean_del_object(v___x_2080_);
lean_dec(v_a_2078_);
lean_del_object(v___x_2075_);
v___x_2090_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2064_ = v_tail_2073_;
v_b_2065_ = v___x_2090_;
goto _start;
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_del_object(v___x_2075_);
lean_dec(v_tail_2073_);
lean_dec(v_declName_2063_);
v_a_2093_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2077_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2077_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2102_, lean_object* v_as_x27_2103_, lean_object* v_b_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2102_, v_as_x27_2103_, v_b_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2111_, lean_object* v_declName_2112_, uint8_t v_nonRec_2113_, lean_object* v___x_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2123_; lean_object* v_env_2124_; uint8_t v___x_2125_; uint8_t v___x_2126_; 
v___x_2123_ = lean_st_ref_get(v___y_2118_);
v_env_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc_ref(v_env_2124_);
lean_dec(v___x_2123_);
v___x_2125_ = 1;
lean_inc(v___x_2111_);
v___x_2126_ = l_Lean_Environment_contains(v_env_2124_, v___x_2111_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_dec(v___x_2111_);
lean_inc(v_declName_2112_);
v___x_2127_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2112_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; uint8_t v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = lean_unbox(v_a_2128_);
lean_dec(v_a_2128_);
if (v___x_2129_ == 0)
{
lean_dec_ref(v___x_2114_);
lean_dec(v_declName_2112_);
goto v___jp_2120_;
}
else
{
lean_object* v___x_2130_; 
lean_inc(v_declName_2112_);
v___x_2130_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2112_, v___y_2118_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; uint8_t v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = lean_unbox(v_a_2131_);
lean_dec(v_a_2131_);
if (v___x_2132_ == 0)
{
if (v_nonRec_2113_ == 0)
{
lean_dec_ref(v___x_2114_);
lean_dec(v_declName_2112_);
goto v___jp_2120_;
}
else
{
lean_object* v___x_2133_; lean_object* v_env_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2133_ = lean_st_ref_get(v___y_2118_);
v_env_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc_ref(v_env_2134_);
lean_dec(v___x_2133_);
lean_inc(v_declName_2112_);
v___x_2135_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2134_, v_declName_2112_, v___x_2114_);
v___x_2136_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2112_, v___x_2135_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2136_;
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec_ref(v___x_2114_);
v___x_2137_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2138_ = lean_st_ref_get(v___x_2137_);
v___x_2139_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2140_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2112_, v___x_2138_, v___x_2139_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2150_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2150_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2150_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_fst_2145_; 
v_fst_2145_ = lean_ctor_get(v_a_2141_, 0);
lean_inc(v_fst_2145_);
lean_dec(v_a_2141_);
if (lean_obj_tag(v_fst_2145_) == 0)
{
lean_del_object(v___x_2143_);
goto v___jp_2120_;
}
else
{
lean_object* v_val_2146_; lean_object* v___x_2148_; 
v_val_2146_ = lean_ctor_get(v_fst_2145_, 0);
lean_inc(v_val_2146_);
lean_dec_ref(v_fst_2145_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v_val_2146_);
v___x_2148_ = v___x_2143_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_val_2146_);
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
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_a_2151_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2140_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2140_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v___x_2114_);
lean_dec(v_declName_2112_);
v_a_2159_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2130_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2130_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v___x_2114_);
lean_dec(v_declName_2112_);
v_a_2167_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2127_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2127_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v___x_2114_);
lean_dec(v_declName_2112_);
v___x_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2111_);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
return v___x_2176_;
}
v___jp_2120_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2177_, lean_object* v_declName_2178_, lean_object* v_nonRec_2179_, lean_object* v___x_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
uint8_t v_nonRec_boxed_2186_; lean_object* v_res_2187_; 
v_nonRec_boxed_2186_ = lean_unbox(v_nonRec_2179_);
v_res_2187_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2177_, v_declName_2178_, v_nonRec_boxed_2186_, v___x_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_ref_2194_; lean_object* v___x_2195_; lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2204_; 
v_ref_2194_ = lean_ctor_get(v___y_2191_, 5);
v___x_2195_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msg_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
lean_inc(v_ref_2194_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_ref_2194_);
lean_ctor_set(v___x_2200_, 1, v_a_2196_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 1);
lean_ctor_set(v___x_2198_, 0, v___x_2200_);
v___x_2202_ = v___x_2198_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2212_, uint8_t v_isExporting_2213_, lean_object* v___x_2214_, lean_object* v___y_2215_, lean_object* v___x_2216_, lean_object* v_a_x3f_2217_){
_start:
{
lean_object* v___x_2219_; lean_object* v_env_2220_; lean_object* v_nextMacroScope_2221_; lean_object* v_ngen_2222_; lean_object* v_auxDeclNGen_2223_; lean_object* v_traceState_2224_; lean_object* v_messages_2225_; lean_object* v_infoState_2226_; lean_object* v_snapshotTasks_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2252_; 
v___x_2219_ = lean_st_ref_take(v___y_2212_);
v_env_2220_ = lean_ctor_get(v___x_2219_, 0);
v_nextMacroScope_2221_ = lean_ctor_get(v___x_2219_, 1);
v_ngen_2222_ = lean_ctor_get(v___x_2219_, 2);
v_auxDeclNGen_2223_ = lean_ctor_get(v___x_2219_, 3);
v_traceState_2224_ = lean_ctor_get(v___x_2219_, 4);
v_messages_2225_ = lean_ctor_get(v___x_2219_, 6);
v_infoState_2226_ = lean_ctor_get(v___x_2219_, 7);
v_snapshotTasks_2227_ = lean_ctor_get(v___x_2219_, 8);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; 
v_unused_2253_ = lean_ctor_get(v___x_2219_, 5);
lean_dec(v_unused_2253_);
v___x_2229_ = v___x_2219_;
v_isShared_2230_ = v_isSharedCheck_2252_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_snapshotTasks_2227_);
lean_inc(v_infoState_2226_);
lean_inc(v_messages_2225_);
lean_inc(v_traceState_2224_);
lean_inc(v_auxDeclNGen_2223_);
lean_inc(v_ngen_2222_);
lean_inc(v_nextMacroScope_2221_);
lean_inc(v_env_2220_);
lean_dec(v___x_2219_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2252_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_Environment_setExporting(v_env_2220_, v_isExporting_2213_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 5, v___x_2214_);
lean_ctor_set(v___x_2229_, 0, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_nextMacroScope_2221_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_ngen_2222_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_auxDeclNGen_2223_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v_traceState_2224_);
lean_ctor_set(v_reuseFailAlloc_2251_, 5, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2251_, 6, v_messages_2225_);
lean_ctor_set(v_reuseFailAlloc_2251_, 7, v_infoState_2226_);
lean_ctor_set(v_reuseFailAlloc_2251_, 8, v_snapshotTasks_2227_);
v___x_2233_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_mctx_2236_; lean_object* v_zetaDeltaFVarIds_2237_; lean_object* v_postponed_2238_; lean_object* v_diag_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2249_; 
v___x_2234_ = lean_st_ref_set(v___y_2212_, v___x_2233_);
v___x_2235_ = lean_st_ref_take(v___y_2215_);
v_mctx_2236_ = lean_ctor_get(v___x_2235_, 0);
v_zetaDeltaFVarIds_2237_ = lean_ctor_get(v___x_2235_, 2);
v_postponed_2238_ = lean_ctor_get(v___x_2235_, 3);
v_diag_2239_ = lean_ctor_get(v___x_2235_, 4);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v___x_2235_, 1);
lean_dec(v_unused_2250_);
v___x_2241_ = v___x_2235_;
v_isShared_2242_ = v_isSharedCheck_2249_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_diag_2239_);
lean_inc(v_postponed_2238_);
lean_inc(v_zetaDeltaFVarIds_2237_);
lean_inc(v_mctx_2236_);
lean_dec(v___x_2235_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2249_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v___x_2216_);
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_mctx_2236_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_zetaDeltaFVarIds_2237_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_postponed_2238_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v_diag_2239_);
v___x_2244_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_st_ref_set(v___y_2215_, v___x_2244_);
v___x_2246_ = lean_box(0);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
return v___x_2247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2254_, lean_object* v_isExporting_2255_, lean_object* v___x_2256_, lean_object* v___y_2257_, lean_object* v___x_2258_, lean_object* v_a_x3f_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_isExporting_boxed_2261_; lean_object* v_res_2262_; 
v_isExporting_boxed_2261_ = lean_unbox(v_isExporting_2255_);
v_res_2262_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2254_, v_isExporting_boxed_2261_, v___x_2256_, v___y_2257_, v___x_2258_, v_a_x3f_2259_);
lean_dec(v_a_x3f_2259_);
lean_dec(v___y_2257_);
lean_dec(v___y_2254_);
return v_res_2262_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_2264_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
lean_ctor_set(v___x_2264_, 2, v___x_2263_);
lean_ctor_set(v___x_2264_, 3, v___x_2263_);
lean_ctor_set(v___x_2264_, 4, v___x_2263_);
lean_ctor_set(v___x_2264_, 5, v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2265_, uint8_t v_isExporting_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; lean_object* v_env_2273_; uint8_t v_isExporting_2274_; lean_object* v___x_2275_; lean_object* v_env_2276_; lean_object* v_nextMacroScope_2277_; lean_object* v_ngen_2278_; lean_object* v_auxDeclNGen_2279_; lean_object* v_traceState_2280_; lean_object* v_messages_2281_; lean_object* v_infoState_2282_; lean_object* v_snapshotTasks_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2337_; 
v___x_2272_ = lean_st_ref_get(v___y_2270_);
v_env_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc_ref(v_env_2273_);
lean_dec(v___x_2272_);
v_isExporting_2274_ = lean_ctor_get_uint8(v_env_2273_, sizeof(void*)*8);
lean_dec_ref(v_env_2273_);
v___x_2275_ = lean_st_ref_take(v___y_2270_);
v_env_2276_ = lean_ctor_get(v___x_2275_, 0);
v_nextMacroScope_2277_ = lean_ctor_get(v___x_2275_, 1);
v_ngen_2278_ = lean_ctor_get(v___x_2275_, 2);
v_auxDeclNGen_2279_ = lean_ctor_get(v___x_2275_, 3);
v_traceState_2280_ = lean_ctor_get(v___x_2275_, 4);
v_messages_2281_ = lean_ctor_get(v___x_2275_, 6);
v_infoState_2282_ = lean_ctor_get(v___x_2275_, 7);
v_snapshotTasks_2283_ = lean_ctor_get(v___x_2275_, 8);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v___x_2275_, 5);
lean_dec(v_unused_2338_);
v___x_2285_ = v___x_2275_;
v_isShared_2286_ = v_isSharedCheck_2337_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_snapshotTasks_2283_);
lean_inc(v_infoState_2282_);
lean_inc(v_messages_2281_);
lean_inc(v_traceState_2280_);
lean_inc(v_auxDeclNGen_2279_);
lean_inc(v_ngen_2278_);
lean_inc(v_nextMacroScope_2277_);
lean_inc(v_env_2276_);
lean_dec(v___x_2275_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2337_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2287_ = l_Lean_Environment_setExporting(v_env_2276_, v_isExporting_2266_);
v___x_2288_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 5, v___x_2288_);
lean_ctor_set(v___x_2285_, 0, v___x_2287_);
v___x_2290_ = v___x_2285_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_nextMacroScope_2277_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_ngen_2278_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_auxDeclNGen_2279_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_traceState_2280_);
lean_ctor_set(v_reuseFailAlloc_2336_, 5, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2336_, 6, v_messages_2281_);
lean_ctor_set(v_reuseFailAlloc_2336_, 7, v_infoState_2282_);
lean_ctor_set(v_reuseFailAlloc_2336_, 8, v_snapshotTasks_2283_);
v___x_2290_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_mctx_2293_; lean_object* v_zetaDeltaFVarIds_2294_; lean_object* v_postponed_2295_; lean_object* v_diag_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2334_; 
v___x_2291_ = lean_st_ref_set(v___y_2270_, v___x_2290_);
v___x_2292_ = lean_st_ref_take(v___y_2268_);
v_mctx_2293_ = lean_ctor_get(v___x_2292_, 0);
v_zetaDeltaFVarIds_2294_ = lean_ctor_get(v___x_2292_, 2);
v_postponed_2295_ = lean_ctor_get(v___x_2292_, 3);
v_diag_2296_ = lean_ctor_get(v___x_2292_, 4);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v___x_2292_, 1);
lean_dec(v_unused_2335_);
v___x_2298_ = v___x_2292_;
v_isShared_2299_ = v_isSharedCheck_2334_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_diag_2296_);
lean_inc(v_postponed_2295_);
lean_inc(v_zetaDeltaFVarIds_2294_);
lean_inc(v_mctx_2293_);
lean_dec(v___x_2292_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2334_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_mctx_2293_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_zetaDeltaFVarIds_2294_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_postponed_2295_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_diag_2296_);
v___x_2302_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v_r_2304_; 
v___x_2303_ = lean_st_ref_set(v___y_2268_, v___x_2302_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
v_r_2304_ = lean_apply_5(v_x_2265_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, lean_box(0));
if (lean_obj_tag(v_r_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2321_; 
v_a_2305_ = lean_ctor_get(v_r_2304_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_r_2304_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2307_ = v_r_2304_;
v_isShared_2308_ = v_isSharedCheck_2321_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v_r_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2321_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
lean_inc(v_a_2305_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set_tag(v___x_2307_, 1);
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v___x_2311_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2270_, v_isExporting_2274_, v___x_2288_, v___y_2268_, v___x_2300_, v___x_2310_);
lean_dec_ref(v___x_2310_);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v___x_2311_, 0);
lean_dec(v_unused_2319_);
v___x_2313_ = v___x_2311_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_dec(v___x_2311_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v_a_2305_);
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2305_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
v_a_2322_ = lean_ctor_get(v_r_2304_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v_r_2304_);
v___x_2323_ = lean_box(0);
v___x_2324_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2270_, v_isExporting_2274_, v___x_2288_, v___y_2268_, v___x_2300_, v___x_2323_);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2331_ == 0)
{
lean_object* v_unused_2332_; 
v_unused_2332_ = lean_ctor_get(v___x_2324_, 0);
lean_dec(v_unused_2332_);
v___x_2326_ = v___x_2324_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_dec(v___x_2324_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set_tag(v___x_2326_, 1);
lean_ctor_set(v___x_2326_, 0, v_a_2322_);
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2322_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2339_, lean_object* v_isExporting_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v_isExporting_boxed_2346_; lean_object* v_res_2347_; 
v_isExporting_boxed_2346_ = lean_unbox(v_isExporting_2340_);
v_res_2347_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2339_, v_isExporting_boxed_2346_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2348_, uint8_t v_when_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
if (v_when_2349_ == 0)
{
lean_object* v___x_2355_; 
lean_inc(v___y_2353_);
lean_inc_ref(v___y_2352_);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
v___x_2355_ = lean_apply_5(v_x_2348_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, lean_box(0));
return v___x_2355_;
}
else
{
uint8_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = 0;
v___x_2357_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2348_, v___x_2356_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2358_, lean_object* v_when_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v_when_boxed_2365_; lean_object* v_res_2366_; 
v_when_boxed_2365_ = lean_unbox(v_when_2359_);
v_res_2366_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2358_, v_when_boxed_2365_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2366_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2369_ = l_Lean_stringToMessageData(v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2372_ = l_Lean_stringToMessageData(v___x_2371_);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2375_ = l_Lean_stringToMessageData(v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2376_, uint8_t v_nonRec_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v_env_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___f_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; 
v___x_2383_ = lean_st_ref_get(v___y_2381_);
v_env_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc_ref(v_env_2384_);
lean_dec(v___x_2383_);
v___x_2385_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2376_);
v___x_2386_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2384_, v_declName_2376_, v___x_2385_);
v___x_2387_ = lean_box(v_nonRec_2377_);
lean_inc(v___x_2386_);
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2388_, 0, v___x_2386_);
lean_closure_set(v___f_2388_, 1, v_declName_2376_);
lean_closure_set(v___f_2388_, 2, v___x_2387_);
lean_closure_set(v___f_2388_, 3, v___x_2385_);
v___x_2389_ = 1;
v___x_2390_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2388_, v___x_2389_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
if (lean_obj_tag(v_a_2391_) == 1)
{
lean_object* v_val_2392_; uint8_t v___x_2393_; 
v_val_2392_ = lean_ctor_get(v_a_2391_, 0);
lean_inc(v_val_2392_);
lean_dec_ref(v_a_2391_);
v___x_2393_ = lean_name_eq(v_val_2392_, v___x_2386_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v___x_2390_);
v___x_2394_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2395_ = l_Lean_MessageData_ofName(v_val_2392_);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = l_Lean_MessageData_ofName(v___x_2386_);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2402_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
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
else
{
lean_dec(v_val_2392_);
lean_dec(v___x_2386_);
return v___x_2390_;
}
}
else
{
lean_dec(v_a_2391_);
lean_dec(v___x_2386_);
return v___x_2390_;
}
}
else
{
lean_dec(v___x_2386_);
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2412_, lean_object* v_nonRec_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v_nonRec_boxed_2419_; lean_object* v_res_2420_; 
v_nonRec_boxed_2419_ = lean_unbox(v_nonRec_2413_);
v_res_2420_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2412_, v_nonRec_boxed_2419_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2421_, uint8_t v_nonRec_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2428_ = lean_box(v_nonRec_2422_);
v___f_2429_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2429_, 0, v_declName_2421_);
lean_closure_set(v___f_2429_, 1, v___x_2428_);
v___x_2430_ = lean_unsigned_to_nat(32u);
v___x_2431_ = lean_mk_empty_array_with_capacity(v___x_2430_);
lean_dec_ref(v___x_2431_);
v___x_2432_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2434_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2432_, v___x_2433_, v___f_2429_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2435_, lean_object* v_nonRec_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
uint8_t v_nonRec_boxed_2442_; lean_object* v_res_2443_; 
v_nonRec_boxed_2442_ = lean_unbox(v_nonRec_2436_);
v_res_2443_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2435_, v_nonRec_boxed_2442_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2444_, lean_object* v_as_2445_, lean_object* v_as_x27_2446_, lean_object* v_b_2447_, lean_object* v_a_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2444_, v_as_x27_2446_, v_b_2447_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2455_, lean_object* v_as_2456_, lean_object* v_as_x27_2457_, lean_object* v_b_2458_, lean_object* v_a_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2455_, v_as_2456_, v_as_x27_2457_, v_b_2458_, v_a_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v_as_2456_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2466_, lean_object* v_x_2467_, uint8_t v_isExporting_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2467_, v_isExporting_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2475_, lean_object* v_x_2476_, lean_object* v_isExporting_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
uint8_t v_isExporting_boxed_2483_; lean_object* v_res_2484_; 
v_isExporting_boxed_2483_ = lean_unbox(v_isExporting_2477_);
v_res_2484_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2475_, v_x_2476_, v_isExporting_boxed_2483_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2485_, lean_object* v_x_2486_, uint8_t v_when_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2486_, v_when_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_x_2495_, lean_object* v_when_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_when_boxed_2502_; lean_object* v_res_2503_; 
v_when_boxed_2502_ = lean_unbox(v_when_2496_);
v_res_2503_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2494_, v_x_2495_, v_when_boxed_2502_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2504_, lean_object* v_msg_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2512_, lean_object* v_msg_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2512_, v_msg_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v_cls_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_options_2523_; uint8_t v_hasTrace_2524_; 
v_options_2523_ = lean_ctor_get(v___y_2521_, 2);
v_hasTrace_2524_ = lean_ctor_get_uint8(v_options_2523_, sizeof(void*)*1);
if (v_hasTrace_2524_ == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec(v_cls_2520_);
v___x_2525_ = lean_box(v_hasTrace_2524_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
else
{
lean_object* v_inheritedTraceOptions_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_inheritedTraceOptions_2527_ = lean_ctor_get(v___y_2521_, 13);
v___x_2528_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_2529_ = l_Lean_Name_append(v___x_2528_, v_cls_2520_);
v___x_2530_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2527_, v_options_2523_, v___x_2529_);
lean_dec(v___x_2529_);
v___x_2531_ = lean_box(v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_cls_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v_cls_2533_, v___y_2534_);
lean_dec_ref(v___y_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v_cls_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v_cls_2537_, v___y_2538_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v_cls_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v_cls_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
return v_res_2546_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_unsigned_to_nat(32u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2550_ = ((size_t)5ULL);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_unsigned_to_nat(32u);
v___x_2553_ = lean_mk_empty_array_with_capacity(v___x_2552_);
v___x_2554_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_2555_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___x_2553_);
lean_ctor_set(v___x_2555_, 2, v___x_2551_);
lean_ctor_set(v___x_2555_, 3, v___x_2551_);
lean_ctor_set_usize(v___x_2555_, 4, v___x_2550_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; lean_object* v_traceState_2559_; lean_object* v_traces_2560_; lean_object* v___x_2561_; lean_object* v_traceState_2562_; lean_object* v_env_2563_; lean_object* v_nextMacroScope_2564_; lean_object* v_ngen_2565_; lean_object* v_auxDeclNGen_2566_; lean_object* v_cache_2567_; lean_object* v_messages_2568_; lean_object* v_infoState_2569_; lean_object* v_snapshotTasks_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2589_; 
v___x_2558_ = lean_st_ref_get(v___y_2556_);
v_traceState_2559_ = lean_ctor_get(v___x_2558_, 4);
lean_inc_ref(v_traceState_2559_);
lean_dec(v___x_2558_);
v_traces_2560_ = lean_ctor_get(v_traceState_2559_, 0);
lean_inc_ref(v_traces_2560_);
lean_dec_ref(v_traceState_2559_);
v___x_2561_ = lean_st_ref_take(v___y_2556_);
v_traceState_2562_ = lean_ctor_get(v___x_2561_, 4);
v_env_2563_ = lean_ctor_get(v___x_2561_, 0);
v_nextMacroScope_2564_ = lean_ctor_get(v___x_2561_, 1);
v_ngen_2565_ = lean_ctor_get(v___x_2561_, 2);
v_auxDeclNGen_2566_ = lean_ctor_get(v___x_2561_, 3);
v_cache_2567_ = lean_ctor_get(v___x_2561_, 5);
v_messages_2568_ = lean_ctor_get(v___x_2561_, 6);
v_infoState_2569_ = lean_ctor_get(v___x_2561_, 7);
v_snapshotTasks_2570_ = lean_ctor_get(v___x_2561_, 8);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2572_ = v___x_2561_;
v_isShared_2573_ = v_isSharedCheck_2589_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_snapshotTasks_2570_);
lean_inc(v_infoState_2569_);
lean_inc(v_messages_2568_);
lean_inc(v_cache_2567_);
lean_inc(v_traceState_2562_);
lean_inc(v_auxDeclNGen_2566_);
lean_inc(v_ngen_2565_);
lean_inc(v_nextMacroScope_2564_);
lean_inc(v_env_2563_);
lean_dec(v___x_2561_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2589_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
uint64_t v_tid_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2587_; 
v_tid_2574_ = lean_ctor_get_uint64(v_traceState_2562_, sizeof(void*)*1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_traceState_2562_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v_traceState_2562_, 0);
lean_dec(v_unused_2588_);
v___x_2576_ = v_traceState_2562_;
v_isShared_2577_ = v_isSharedCheck_2587_;
goto v_resetjp_2575_;
}
else
{
lean_dec(v_traceState_2562_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2587_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2578_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2578_);
v___x_2580_ = v___x_2576_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2578_);
lean_ctor_set_uint64(v_reuseFailAlloc_2586_, sizeof(void*)*1, v_tid_2574_);
v___x_2580_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2582_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 4, v___x_2580_);
v___x_2582_ = v___x_2572_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_env_2563_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_nextMacroScope_2564_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_ngen_2565_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_auxDeclNGen_2566_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2585_, 5, v_cache_2567_);
lean_ctor_set(v_reuseFailAlloc_2585_, 6, v_messages_2568_);
lean_ctor_set(v_reuseFailAlloc_2585_, 7, v_infoState_2569_);
lean_ctor_set(v_reuseFailAlloc_2585_, 8, v_snapshotTasks_2570_);
v___x_2582_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_st_ref_set(v___y_2556_, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_traces_2560_);
return v___x_2584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_2590_);
lean_dec(v___y_2590_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = 0;
v___x_2606_ = lean_box(v___x_2605_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
return v_res_2612_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2615_ = l_Lean_stringToMessageData(v___x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2616_, lean_object* v_x_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2622_ = l_Lean_MessageData_ofName(v_name_2616_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2625_, lean_object* v_x_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2625_, v_x_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_x_2626_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_x_2631_){
_start:
{
if (lean_obj_tag(v_x_2631_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
v_a_2633_ = lean_ctor_get(v_x_2631_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_x_2631_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v_x_2631_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v_x_2631_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v_x_2631_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_x_2631_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v_x_2631_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v_x_2631_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 0);
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_x_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_x_2649_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(size_t v_sz_2652_, size_t v_i_2653_, lean_object* v_bs_2654_){
_start:
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_usize_dec_lt(v_i_2653_, v_sz_2652_);
if (v___x_2655_ == 0)
{
return v_bs_2654_;
}
else
{
lean_object* v_v_2656_; lean_object* v_msg_2657_; lean_object* v___x_2658_; lean_object* v_bs_x27_2659_; size_t v___x_2660_; size_t v___x_2661_; lean_object* v___x_2662_; 
v_v_2656_ = lean_array_uget_borrowed(v_bs_2654_, v_i_2653_);
v_msg_2657_ = lean_ctor_get(v_v_2656_, 1);
lean_inc_ref(v_msg_2657_);
v___x_2658_ = lean_unsigned_to_nat(0u);
v_bs_x27_2659_ = lean_array_uset(v_bs_2654_, v_i_2653_, v___x_2658_);
v___x_2660_ = ((size_t)1ULL);
v___x_2661_ = lean_usize_add(v_i_2653_, v___x_2660_);
v___x_2662_ = lean_array_uset(v_bs_x27_2659_, v_i_2653_, v_msg_2657_);
v_i_2653_ = v___x_2661_;
v_bs_2654_ = v___x_2662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_sz_2664_, lean_object* v_i_2665_, lean_object* v_bs_2666_){
_start:
{
size_t v_sz_boxed_2667_; size_t v_i_boxed_2668_; lean_object* v_res_2669_; 
v_sz_boxed_2667_ = lean_unbox_usize(v_sz_2664_);
lean_dec(v_sz_2664_);
v_i_boxed_2668_ = lean_unbox_usize(v_i_2665_);
lean_dec(v_i_2665_);
v_res_2669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_sz_boxed_2667_, v_i_boxed_2668_, v_bs_2666_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_oldTraces_2670_, lean_object* v_data_2671_, lean_object* v_ref_2672_, lean_object* v_msg_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_fileName_2677_; lean_object* v_fileMap_2678_; lean_object* v_options_2679_; lean_object* v_currRecDepth_2680_; lean_object* v_maxRecDepth_2681_; lean_object* v_ref_2682_; lean_object* v_currNamespace_2683_; lean_object* v_openDecls_2684_; lean_object* v_initHeartbeats_2685_; lean_object* v_maxHeartbeats_2686_; lean_object* v_quotContext_2687_; lean_object* v_currMacroScope_2688_; uint8_t v_diag_2689_; lean_object* v_cancelTk_x3f_2690_; uint8_t v_suppressElabErrors_2691_; lean_object* v_inheritedTraceOptions_2692_; lean_object* v___x_2693_; lean_object* v_traceState_2694_; lean_object* v_traces_2695_; lean_object* v_ref_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; size_t v_sz_2699_; size_t v___x_2700_; lean_object* v___x_2701_; lean_object* v_msg_2702_; lean_object* v___x_2703_; lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2741_; 
v_fileName_2677_ = lean_ctor_get(v___y_2674_, 0);
v_fileMap_2678_ = lean_ctor_get(v___y_2674_, 1);
v_options_2679_ = lean_ctor_get(v___y_2674_, 2);
v_currRecDepth_2680_ = lean_ctor_get(v___y_2674_, 3);
v_maxRecDepth_2681_ = lean_ctor_get(v___y_2674_, 4);
v_ref_2682_ = lean_ctor_get(v___y_2674_, 5);
v_currNamespace_2683_ = lean_ctor_get(v___y_2674_, 6);
v_openDecls_2684_ = lean_ctor_get(v___y_2674_, 7);
v_initHeartbeats_2685_ = lean_ctor_get(v___y_2674_, 8);
v_maxHeartbeats_2686_ = lean_ctor_get(v___y_2674_, 9);
v_quotContext_2687_ = lean_ctor_get(v___y_2674_, 10);
v_currMacroScope_2688_ = lean_ctor_get(v___y_2674_, 11);
v_diag_2689_ = lean_ctor_get_uint8(v___y_2674_, sizeof(void*)*14);
v_cancelTk_x3f_2690_ = lean_ctor_get(v___y_2674_, 12);
v_suppressElabErrors_2691_ = lean_ctor_get_uint8(v___y_2674_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2692_ = lean_ctor_get(v___y_2674_, 13);
v___x_2693_ = lean_st_ref_get(v___y_2675_);
v_traceState_2694_ = lean_ctor_get(v___x_2693_, 4);
lean_inc_ref(v_traceState_2694_);
lean_dec(v___x_2693_);
v_traces_2695_ = lean_ctor_get(v_traceState_2694_, 0);
lean_inc_ref(v_traces_2695_);
lean_dec_ref(v_traceState_2694_);
v_ref_2696_ = l_Lean_replaceRef(v_ref_2672_, v_ref_2682_);
lean_inc_ref(v_inheritedTraceOptions_2692_);
lean_inc(v_cancelTk_x3f_2690_);
lean_inc(v_currMacroScope_2688_);
lean_inc(v_quotContext_2687_);
lean_inc(v_maxHeartbeats_2686_);
lean_inc(v_initHeartbeats_2685_);
lean_inc(v_openDecls_2684_);
lean_inc(v_currNamespace_2683_);
lean_inc(v_maxRecDepth_2681_);
lean_inc(v_currRecDepth_2680_);
lean_inc_ref(v_options_2679_);
lean_inc_ref(v_fileMap_2678_);
lean_inc_ref(v_fileName_2677_);
v___x_2697_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2697_, 0, v_fileName_2677_);
lean_ctor_set(v___x_2697_, 1, v_fileMap_2678_);
lean_ctor_set(v___x_2697_, 2, v_options_2679_);
lean_ctor_set(v___x_2697_, 3, v_currRecDepth_2680_);
lean_ctor_set(v___x_2697_, 4, v_maxRecDepth_2681_);
lean_ctor_set(v___x_2697_, 5, v_ref_2696_);
lean_ctor_set(v___x_2697_, 6, v_currNamespace_2683_);
lean_ctor_set(v___x_2697_, 7, v_openDecls_2684_);
lean_ctor_set(v___x_2697_, 8, v_initHeartbeats_2685_);
lean_ctor_set(v___x_2697_, 9, v_maxHeartbeats_2686_);
lean_ctor_set(v___x_2697_, 10, v_quotContext_2687_);
lean_ctor_set(v___x_2697_, 11, v_currMacroScope_2688_);
lean_ctor_set(v___x_2697_, 12, v_cancelTk_x3f_2690_);
lean_ctor_set(v___x_2697_, 13, v_inheritedTraceOptions_2692_);
lean_ctor_set_uint8(v___x_2697_, sizeof(void*)*14, v_diag_2689_);
lean_ctor_set_uint8(v___x_2697_, sizeof(void*)*14 + 1, v_suppressElabErrors_2691_);
v___x_2698_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2695_);
lean_dec_ref(v_traces_2695_);
v_sz_2699_ = lean_array_size(v___x_2698_);
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_sz_2699_, v___x_2700_, v___x_2698_);
v_msg_2702_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2702_, 0, v_data_2671_);
lean_ctor_set(v_msg_2702_, 1, v_msg_2673_);
lean_ctor_set(v_msg_2702_, 2, v___x_2701_);
v___x_2703_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2702_, v___x_2697_, v___y_2675_);
lean_dec_ref(v___x_2697_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2741_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2741_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v_traceState_2709_; lean_object* v_env_2710_; lean_object* v_nextMacroScope_2711_; lean_object* v_ngen_2712_; lean_object* v_auxDeclNGen_2713_; lean_object* v_cache_2714_; lean_object* v_messages_2715_; lean_object* v_infoState_2716_; lean_object* v_snapshotTasks_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2740_; 
v___x_2708_ = lean_st_ref_take(v___y_2675_);
v_traceState_2709_ = lean_ctor_get(v___x_2708_, 4);
v_env_2710_ = lean_ctor_get(v___x_2708_, 0);
v_nextMacroScope_2711_ = lean_ctor_get(v___x_2708_, 1);
v_ngen_2712_ = lean_ctor_get(v___x_2708_, 2);
v_auxDeclNGen_2713_ = lean_ctor_get(v___x_2708_, 3);
v_cache_2714_ = lean_ctor_get(v___x_2708_, 5);
v_messages_2715_ = lean_ctor_get(v___x_2708_, 6);
v_infoState_2716_ = lean_ctor_get(v___x_2708_, 7);
v_snapshotTasks_2717_ = lean_ctor_get(v___x_2708_, 8);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2719_ = v___x_2708_;
v_isShared_2720_ = v_isSharedCheck_2740_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_snapshotTasks_2717_);
lean_inc(v_infoState_2716_);
lean_inc(v_messages_2715_);
lean_inc(v_cache_2714_);
lean_inc(v_traceState_2709_);
lean_inc(v_auxDeclNGen_2713_);
lean_inc(v_ngen_2712_);
lean_inc(v_nextMacroScope_2711_);
lean_inc(v_env_2710_);
lean_dec(v___x_2708_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2740_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
uint64_t v_tid_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2738_; 
v_tid_2721_ = lean_ctor_get_uint64(v_traceState_2709_, sizeof(void*)*1);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_traceState_2709_);
if (v_isSharedCheck_2738_ == 0)
{
lean_object* v_unused_2739_; 
v_unused_2739_ = lean_ctor_get(v_traceState_2709_, 0);
lean_dec(v_unused_2739_);
v___x_2723_ = v_traceState_2709_;
v_isShared_2724_ = v_isSharedCheck_2738_;
goto v_resetjp_2722_;
}
else
{
lean_dec(v_traceState_2709_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2738_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v_ref_2672_);
lean_ctor_set(v___x_2725_, 1, v_a_2704_);
v___x_2726_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2670_, v___x_2725_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2726_);
v___x_2728_ = v___x_2723_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2726_);
lean_ctor_set_uint64(v_reuseFailAlloc_2737_, sizeof(void*)*1, v_tid_2721_);
v___x_2728_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 4, v___x_2728_);
v___x_2730_ = v___x_2719_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_env_2710_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_nextMacroScope_2711_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_ngen_2712_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_auxDeclNGen_2713_);
lean_ctor_set(v_reuseFailAlloc_2736_, 4, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2736_, 5, v_cache_2714_);
lean_ctor_set(v_reuseFailAlloc_2736_, 6, v_messages_2715_);
lean_ctor_set(v_reuseFailAlloc_2736_, 7, v_infoState_2716_);
lean_ctor_set(v_reuseFailAlloc_2736_, 8, v_snapshotTasks_2717_);
v___x_2730_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2731_ = lean_st_ref_set(v___y_2675_, v___x_2730_);
v___x_2732_ = lean_box(0);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2732_);
v___x_2734_ = v___x_2706_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_oldTraces_2742_, lean_object* v_data_2743_, lean_object* v_ref_2744_, lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(v_oldTraces_2742_, v_data_2743_, v_ref_2744_, v_msg_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2749_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(lean_object* v_e_2750_){
_start:
{
if (lean_obj_tag(v_e_2750_) == 0)
{
uint8_t v___x_2751_; 
v___x_2751_ = 2;
return v___x_2751_;
}
else
{
lean_object* v_a_2752_; uint8_t v___x_2753_; 
v_a_2752_ = lean_ctor_get(v_e_2750_, 0);
v___x_2753_ = lean_unbox(v_a_2752_);
if (v___x_2753_ == 0)
{
uint8_t v___x_2754_; 
v___x_2754_ = 1;
return v___x_2754_;
}
else
{
uint8_t v___x_2755_; 
v___x_2755_ = 0;
return v___x_2755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2___boxed(lean_object* v_e_2756_){
_start:
{
uint8_t v_res_2757_; lean_object* v_r_2758_; 
v_res_2757_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(v_e_2756_);
lean_dec_ref(v_e_2756_);
v_r_2758_ = lean_box(v_res_2757_);
return v_r_2758_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__0));
v___x_2761_ = l_Lean_stringToMessageData(v___x_2760_);
return v___x_2761_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__2));
v___x_2764_ = l_Lean_stringToMessageData(v___x_2763_);
return v___x_2764_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4(void){
_start:
{
lean_object* v___x_2765_; double v___x_2766_; 
v___x_2765_ = lean_unsigned_to_nat(1000u);
v___x_2766_ = lean_float_of_nat(v___x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(lean_object* v_cls_2767_, uint8_t v_collapsed_2768_, lean_object* v_tag_2769_, lean_object* v_opts_2770_, uint8_t v_clsEnabled_2771_, lean_object* v_oldTraces_2772_, lean_object* v_msg_2773_, lean_object* v_resStartStop_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_fst_2778_; lean_object* v_snd_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2877_; 
v_fst_2778_ = lean_ctor_get(v_resStartStop_2774_, 0);
v_snd_2779_ = lean_ctor_get(v_resStartStop_2774_, 1);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_resStartStop_2774_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2781_ = v_resStartStop_2774_;
v_isShared_2782_ = v_isSharedCheck_2877_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_snd_2779_);
lean_inc(v_fst_2778_);
lean_dec(v_resStartStop_2774_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2877_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v_data_2786_; lean_object* v_fst_2797_; lean_object* v_snd_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2876_; 
v_fst_2797_ = lean_ctor_get(v_snd_2779_, 0);
v_snd_2798_ = lean_ctor_get(v_snd_2779_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_snd_2779_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2800_ = v_snd_2779_;
v_isShared_2801_ = v_isSharedCheck_2876_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_snd_2798_);
lean_inc(v_fst_2797_);
lean_dec(v_snd_2779_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2876_;
goto v_resetjp_2799_;
}
v___jp_2783_:
{
lean_object* v___x_2787_; 
lean_inc(v___y_2784_);
v___x_2787_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(v_oldTraces_2772_, v_data_2786_, v___y_2784_, v___y_2785_, v___y_2775_, v___y_2776_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; 
lean_dec_ref(v___x_2787_);
v___x_2788_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_fst_2778_);
return v___x_2788_;
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_fst_2778_);
v_a_2789_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2787_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2787_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; uint8_t v___x_2803_; lean_object* v___y_2805_; lean_object* v_a_2806_; uint8_t v___y_2830_; double v___y_2861_; 
v___x_2802_ = l_Lean_trace_profiler;
v___x_2803_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2770_, v___x_2802_);
if (v___x_2803_ == 0)
{
v___y_2830_ = v___x_2803_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2866_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2867_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2770_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; double v___x_2870_; double v___x_2871_; double v___x_2872_; 
v___x_2868_ = l_Lean_trace_profiler_threshold;
v___x_2869_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2770_, v___x_2868_);
v___x_2870_ = lean_float_of_nat(v___x_2869_);
v___x_2871_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4);
v___x_2872_ = lean_float_div(v___x_2870_, v___x_2871_);
v___y_2861_ = v___x_2872_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; double v___x_2875_; 
v___x_2873_ = l_Lean_trace_profiler_threshold;
v___x_2874_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2770_, v___x_2873_);
v___x_2875_ = lean_float_of_nat(v___x_2874_);
v___y_2861_ = v___x_2875_;
goto v___jp_2860_;
}
}
v___jp_2804_:
{
uint8_t v_result_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v_result_2807_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(v_fst_2778_);
v___x_2808_ = l_Lean_TraceResult_toEmoji(v_result_2807_);
v___x_2809_ = l_Lean_stringToMessageData(v___x_2808_);
v___x_2810_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1);
if (v_isShared_2801_ == 0)
{
lean_ctor_set_tag(v___x_2800_, 7);
lean_ctor_set(v___x_2800_, 1, v___x_2810_);
lean_ctor_set(v___x_2800_, 0, v___x_2809_);
v___x_2812_ = v___x_2800_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v_m_2814_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set_tag(v___x_2781_, 7);
lean_ctor_set(v___x_2781_, 1, v_a_2806_);
lean_ctor_set(v___x_2781_, 0, v___x_2812_);
v_m_2814_ = v___x_2781_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_a_2806_);
v_m_2814_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; double v___x_2817_; lean_object* v_data_2818_; 
v___x_2815_ = lean_box(v_result_2807_);
v___x_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
v___x_2817_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0);
lean_inc_ref(v_tag_2769_);
lean_inc_ref(v___x_2816_);
lean_inc(v_cls_2767_);
v_data_2818_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2818_, 0, v_cls_2767_);
lean_ctor_set(v_data_2818_, 1, v___x_2816_);
lean_ctor_set(v_data_2818_, 2, v_tag_2769_);
lean_ctor_set_float(v_data_2818_, sizeof(void*)*3, v___x_2817_);
lean_ctor_set_float(v_data_2818_, sizeof(void*)*3 + 8, v___x_2817_);
lean_ctor_set_uint8(v_data_2818_, sizeof(void*)*3 + 16, v_collapsed_2768_);
if (v___x_2803_ == 0)
{
lean_dec_ref(v___x_2816_);
lean_dec(v_snd_2798_);
lean_dec(v_fst_2797_);
lean_dec_ref(v_tag_2769_);
lean_dec(v_cls_2767_);
v___y_2784_ = v___y_2805_;
v___y_2785_ = v_m_2814_;
v_data_2786_ = v_data_2818_;
goto v___jp_2783_;
}
else
{
lean_object* v_data_2819_; double v___x_2820_; double v___x_2821_; 
lean_dec_ref(v_data_2818_);
v_data_2819_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2819_, 0, v_cls_2767_);
lean_ctor_set(v_data_2819_, 1, v___x_2816_);
lean_ctor_set(v_data_2819_, 2, v_tag_2769_);
v___x_2820_ = lean_unbox_float(v_fst_2797_);
lean_dec(v_fst_2797_);
lean_ctor_set_float(v_data_2819_, sizeof(void*)*3, v___x_2820_);
v___x_2821_ = lean_unbox_float(v_snd_2798_);
lean_dec(v_snd_2798_);
lean_ctor_set_float(v_data_2819_, sizeof(void*)*3 + 8, v___x_2821_);
lean_ctor_set_uint8(v_data_2819_, sizeof(void*)*3 + 16, v_collapsed_2768_);
v___y_2784_ = v___y_2805_;
v___y_2785_ = v_m_2814_;
v_data_2786_ = v_data_2819_;
goto v___jp_2783_;
}
}
}
}
v___jp_2824_:
{
lean_object* v_ref_2825_; lean_object* v___x_2826_; 
v_ref_2825_ = lean_ctor_get(v___y_2775_, 5);
lean_inc(v___y_2776_);
lean_inc_ref(v___y_2775_);
lean_inc(v_fst_2778_);
v___x_2826_ = lean_apply_4(v_msg_2773_, v_fst_2778_, v___y_2775_, v___y_2776_, lean_box(0));
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2826_);
v___y_2805_ = v_ref_2825_;
v_a_2806_ = v_a_2827_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2828_; 
lean_dec_ref(v___x_2826_);
v___x_2828_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3);
v___y_2805_ = v_ref_2825_;
v_a_2806_ = v___x_2828_;
goto v___jp_2804_;
}
}
v___jp_2829_:
{
if (v_clsEnabled_2771_ == 0)
{
if (v___y_2830_ == 0)
{
lean_object* v___x_2831_; lean_object* v_traceState_2832_; lean_object* v_env_2833_; lean_object* v_nextMacroScope_2834_; lean_object* v_ngen_2835_; lean_object* v_auxDeclNGen_2836_; lean_object* v_cache_2837_; lean_object* v_messages_2838_; lean_object* v_infoState_2839_; lean_object* v_snapshotTasks_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2859_; 
lean_del_object(v___x_2800_);
lean_dec(v_snd_2798_);
lean_dec(v_fst_2797_);
lean_del_object(v___x_2781_);
lean_dec_ref(v_msg_2773_);
lean_dec_ref(v_tag_2769_);
lean_dec(v_cls_2767_);
v___x_2831_ = lean_st_ref_take(v___y_2776_);
v_traceState_2832_ = lean_ctor_get(v___x_2831_, 4);
v_env_2833_ = lean_ctor_get(v___x_2831_, 0);
v_nextMacroScope_2834_ = lean_ctor_get(v___x_2831_, 1);
v_ngen_2835_ = lean_ctor_get(v___x_2831_, 2);
v_auxDeclNGen_2836_ = lean_ctor_get(v___x_2831_, 3);
v_cache_2837_ = lean_ctor_get(v___x_2831_, 5);
v_messages_2838_ = lean_ctor_get(v___x_2831_, 6);
v_infoState_2839_ = lean_ctor_get(v___x_2831_, 7);
v_snapshotTasks_2840_ = lean_ctor_get(v___x_2831_, 8);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2842_ = v___x_2831_;
v_isShared_2843_ = v_isSharedCheck_2859_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_snapshotTasks_2840_);
lean_inc(v_infoState_2839_);
lean_inc(v_messages_2838_);
lean_inc(v_cache_2837_);
lean_inc(v_traceState_2832_);
lean_inc(v_auxDeclNGen_2836_);
lean_inc(v_ngen_2835_);
lean_inc(v_nextMacroScope_2834_);
lean_inc(v_env_2833_);
lean_dec(v___x_2831_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2859_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
uint64_t v_tid_2844_; lean_object* v_traces_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2858_; 
v_tid_2844_ = lean_ctor_get_uint64(v_traceState_2832_, sizeof(void*)*1);
v_traces_2845_ = lean_ctor_get(v_traceState_2832_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_traceState_2832_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2847_ = v_traceState_2832_;
v_isShared_2848_ = v_isSharedCheck_2858_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_traces_2845_);
lean_dec(v_traceState_2832_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2858_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2849_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2772_, v_traces_2845_);
lean_dec_ref(v_traces_2845_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2849_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2849_);
lean_ctor_set_uint64(v_reuseFailAlloc_2857_, sizeof(void*)*1, v_tid_2844_);
v___x_2851_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2853_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 4, v___x_2851_);
v___x_2853_ = v___x_2842_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_env_2833_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_nextMacroScope_2834_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_ngen_2835_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_auxDeclNGen_2836_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2856_, 5, v_cache_2837_);
lean_ctor_set(v_reuseFailAlloc_2856_, 6, v_messages_2838_);
lean_ctor_set(v_reuseFailAlloc_2856_, 7, v_infoState_2839_);
lean_ctor_set(v_reuseFailAlloc_2856_, 8, v_snapshotTasks_2840_);
v___x_2853_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_st_ref_set(v___y_2776_, v___x_2853_);
v___x_2855_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_fst_2778_);
return v___x_2855_;
}
}
}
}
}
else
{
goto v___jp_2824_;
}
}
else
{
goto v___jp_2824_;
}
}
v___jp_2860_:
{
double v___x_2862_; double v___x_2863_; double v___x_2864_; uint8_t v___x_2865_; 
v___x_2862_ = lean_unbox_float(v_snd_2798_);
v___x_2863_ = lean_unbox_float(v_fst_2797_);
v___x_2864_ = lean_float_sub(v___x_2862_, v___x_2863_);
v___x_2865_ = lean_float_decLt(v___y_2861_, v___x_2864_);
v___y_2830_ = v___x_2865_;
goto v___jp_2829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_2878_, lean_object* v_collapsed_2879_, lean_object* v_tag_2880_, lean_object* v_opts_2881_, lean_object* v_clsEnabled_2882_, lean_object* v_oldTraces_2883_, lean_object* v_msg_2884_, lean_object* v_resStartStop_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
uint8_t v_collapsed_boxed_2889_; uint8_t v_clsEnabled_boxed_2890_; lean_object* v_res_2891_; 
v_collapsed_boxed_2889_ = lean_unbox(v_collapsed_2879_);
v_clsEnabled_boxed_2890_ = lean_unbox(v_clsEnabled_2882_);
v_res_2891_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v_cls_2878_, v_collapsed_boxed_2889_, v_tag_2880_, v_opts_2881_, v_clsEnabled_boxed_2890_, v_oldTraces_2883_, v_msg_2884_, v_resStartStop_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v_opts_2881_);
return v_res_2891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2895_ = lean_unsigned_to_nat(0u);
v___x_2896_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
lean_ctor_set(v___x_2896_, 2, v___x_2895_);
lean_ctor_set(v___x_2896_, 3, v___x_2894_);
lean_ctor_set(v___x_2896_, 4, v___x_2894_);
lean_ctor_set(v___x_2896_, 5, v___x_2894_);
lean_ctor_set(v___x_2896_, 6, v___x_2894_);
lean_ctor_set(v___x_2896_, 7, v___x_2894_);
lean_ctor_set(v___x_2896_, 8, v___x_2894_);
return v___x_2896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2898_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
lean_ctor_set(v___x_2898_, 2, v___x_2897_);
lean_ctor_set(v___x_2898_, 3, v___x_2897_);
lean_ctor_set(v___x_2898_, 4, v___x_2897_);
lean_ctor_set(v___x_2898_, 5, v___x_2897_);
return v___x_2898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
lean_ctor_set(v___x_2900_, 2, v___x_2899_);
lean_ctor_set(v___x_2900_, 3, v___x_2899_);
lean_ctor_set(v___x_2900_, 4, v___x_2899_);
return v___x_2900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2901_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2902_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_2903_ = lean_box(1);
v___x_2904_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2905_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v___x_2904_);
lean_ctor_set(v___x_2906_, 2, v___x_2903_);
lean_ctor_set(v___x_2906_, 3, v___x_2902_);
lean_ctor_set(v___x_2906_, 4, v___x_2901_);
return v___x_2906_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2910_; double v___x_2911_; 
v___x_2910_ = lean_unsigned_to_nat(1000000000u);
v___x_2911_ = lean_float_of_nat(v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_2912_, lean_object* v_name_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_options_2917_; uint8_t v_hasTrace_2918_; 
v_options_2917_ = lean_ctor_get(v___y_2914_, 2);
v_hasTrace_2918_ = lean_ctor_get_uint8(v_options_2917_, sizeof(void*)*1);
if (v_hasTrace_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v_env_2920_; lean_object* v___x_2921_; 
lean_dec_ref(v___f_2912_);
v___x_2919_ = lean_st_ref_get(v___y_2915_);
v_env_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc_ref(v_env_2920_);
lean_dec(v___x_2919_);
lean_inc(v_name_2913_);
v___x_2921_ = l_Lean_Meta_declFromEqLikeName(v_env_2920_, v_name_2913_);
if (lean_obj_tag(v___x_2921_) == 1)
{
lean_object* v_val_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_3021_; 
v_val_2922_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2924_ = v___x_2921_;
v_isShared_2925_ = v_isSharedCheck_3021_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_val_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_3021_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v_fst_2926_; lean_object* v_snd_2927_; lean_object* v___x_2928_; lean_object* v_env_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v_fst_2926_ = lean_ctor_get(v_val_2922_, 0);
lean_inc(v_fst_2926_);
v_snd_2927_ = lean_ctor_get(v_val_2922_, 1);
lean_inc(v_snd_2927_);
lean_dec(v_val_2922_);
v___x_2928_ = lean_st_ref_get(v___y_2915_);
v_env_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc_ref(v_env_2929_);
lean_dec(v___x_2928_);
lean_inc(v_snd_2927_);
lean_inc(v_fst_2926_);
v___x_2930_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2929_, v_fst_2926_, v_snd_2927_);
v___x_2931_ = lean_name_eq(v_name_2913_, v___x_2930_);
lean_dec(v___x_2930_);
lean_dec(v_name_2913_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
lean_dec(v_snd_2927_);
lean_dec(v_fst_2926_);
v___x_2932_ = lean_box(v_hasTrace_2918_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2932_);
v___x_2934_ = v___x_2924_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
else
{
uint8_t v___x_2936_; lean_object* v_a_2938_; 
lean_inc(v_snd_2927_);
v___x_2936_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_2927_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2952_; uint8_t v___x_2953_; lean_object* v_a_2955_; 
lean_del_object(v___x_2924_);
v___x_2952_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_2953_ = lean_string_dec_eq(v_snd_2927_, v___x_2952_);
lean_dec(v_snd_2927_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_dec(v_fst_2926_);
v___x_2967_ = lean_box(v_hasTrace_2918_);
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
return v___x_2968_;
}
else
{
uint8_t v___x_2969_; uint8_t v___x_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; uint64_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2969_ = 1;
v___x_2970_ = 0;
v___x_2971_ = 2;
v___x_2972_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2972_, 0, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2972_, 1, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2972_, 2, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2972_, 3, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2972_, 4, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2972_, 5, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 6, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 7, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2972_, 8, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 9, v___x_2969_);
lean_ctor_set_uint8(v___x_2972_, 10, v___x_2970_);
lean_ctor_set_uint8(v___x_2972_, 11, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 12, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 13, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 14, v___x_2971_);
lean_ctor_set_uint8(v___x_2972_, 15, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 16, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 17, v___x_2953_);
lean_ctor_set_uint8(v___x_2972_, 18, v___x_2953_);
v___x_2973_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2972_);
v___x_2974_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set_uint64(v___x_2974_, sizeof(void*)*1, v___x_2973_);
v___x_2975_ = lean_box(1);
v___x_2976_ = lean_unsigned_to_nat(0u);
v___x_2977_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2978_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2980_, 0, v___x_2974_);
lean_ctor_set(v___x_2980_, 1, v___x_2975_);
lean_ctor_set(v___x_2980_, 2, v___x_2977_);
lean_ctor_set(v___x_2980_, 3, v___x_2978_);
lean_ctor_set(v___x_2980_, 4, v___x_2979_);
lean_ctor_set(v___x_2980_, 5, v___x_2976_);
lean_ctor_set(v___x_2980_, 6, v___x_2979_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*7, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*7 + 1, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*7 + 2, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*7 + 3, v___x_2931_);
v___x_2981_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2982_ = lean_st_mk_ref(v___x_2981_);
v___x_2983_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_2926_, v___x_2931_, v___x_2980_, v___x_2982_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___x_2980_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref(v___x_2983_);
v___x_2985_ = lean_st_ref_get(v___x_2982_);
lean_dec(v___x_2982_);
lean_dec(v___x_2985_);
v_a_2955_ = v_a_2984_;
goto v___jp_2954_;
}
else
{
lean_dec(v___x_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2986_; 
v_a_2986_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2983_);
v_a_2955_ = v_a_2986_;
goto v___jp_2954_;
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
v_a_2987_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2983_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2983_);
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
}
v___jp_2954_:
{
if (lean_obj_tag(v_a_2955_) == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_box(v_hasTrace_2918_);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
else
{
lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2965_; 
v_isSharedCheck_2965_ = !lean_is_exclusive(v_a_2955_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; 
v_unused_2966_ = lean_ctor_get(v_a_2955_, 0);
lean_dec(v_unused_2966_);
v___x_2959_ = v_a_2955_;
v_isShared_2960_ = v_isSharedCheck_2965_;
goto v_resetjp_2958_;
}
else
{
lean_dec(v_a_2955_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2965_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = lean_box(v___x_2953_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2961_);
v___x_2963_ = v___x_2959_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
else
{
uint8_t v___x_2995_; uint8_t v___x_2996_; uint8_t v___x_2997_; lean_object* v___x_2998_; uint64_t v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec(v_snd_2927_);
v___x_2995_ = 1;
v___x_2996_ = 0;
v___x_2997_ = 2;
v___x_2998_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2998_, 0, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2998_, 1, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2998_, 2, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2998_, 3, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2998_, 4, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2998_, 5, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 6, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 7, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_2998_, 8, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 9, v___x_2995_);
lean_ctor_set_uint8(v___x_2998_, 10, v___x_2996_);
lean_ctor_set_uint8(v___x_2998_, 11, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 12, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 13, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 14, v___x_2997_);
lean_ctor_set_uint8(v___x_2998_, 15, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 16, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 17, v___x_2936_);
lean_ctor_set_uint8(v___x_2998_, 18, v___x_2936_);
v___x_2999_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2998_);
v___x_3000_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set_uint64(v___x_3000_, sizeof(void*)*1, v___x_2999_);
v___x_3001_ = lean_box(1);
v___x_3002_ = lean_unsigned_to_nat(0u);
v___x_3003_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3004_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3006_, 0, v___x_3000_);
lean_ctor_set(v___x_3006_, 1, v___x_3001_);
lean_ctor_set(v___x_3006_, 2, v___x_3003_);
lean_ctor_set(v___x_3006_, 3, v___x_3004_);
lean_ctor_set(v___x_3006_, 4, v___x_3005_);
lean_ctor_set(v___x_3006_, 5, v___x_3002_);
lean_ctor_set(v___x_3006_, 6, v___x_3005_);
lean_ctor_set_uint8(v___x_3006_, sizeof(void*)*7, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3006_, sizeof(void*)*7 + 1, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3006_, sizeof(void*)*7 + 2, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3006_, sizeof(void*)*7 + 3, v___x_2931_);
v___x_3007_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3008_ = lean_st_mk_ref(v___x_3007_);
v___x_3009_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_2926_, v___x_3006_, v___x_3008_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___x_3006_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref(v___x_3009_);
v___x_3011_ = lean_st_ref_get(v___x_3008_);
lean_dec(v___x_3008_);
lean_dec(v___x_3011_);
v_a_2938_ = v_a_3010_;
goto v___jp_2937_;
}
else
{
lean_dec(v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3012_; 
v_a_3012_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3012_);
lean_dec_ref(v___x_3009_);
v_a_2938_ = v_a_3012_;
goto v___jp_2937_;
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_del_object(v___x_2924_);
v_a_3013_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3009_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3009_);
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
}
v___jp_2937_:
{
if (lean_obj_tag(v_a_2938_) == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = lean_box(v_hasTrace_2918_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2939_);
v___x_2941_ = v___x_2924_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
else
{
lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2950_; 
lean_del_object(v___x_2924_);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v_a_2938_, 0);
lean_dec(v_unused_2951_);
v___x_2944_ = v_a_2938_;
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
else
{
lean_dec(v_a_2938_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = lean_box(v___x_2936_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2946_);
v___x_2948_ = v___x_2944_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec(v___x_2921_);
lean_dec(v_name_2913_);
v___x_3022_ = lean_box(v_hasTrace_2918_);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3333_; 
v___x_3024_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3025_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___x_3024_, v___y_2914_);
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3333_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3333_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___f_3030_; lean_object* v___x_3031_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v_a_3035_; lean_object* v___y_3049_; lean_object* v___y_3050_; uint8_t v_a_3051_; lean_object* v___y_3055_; lean_object* v___y_3056_; uint8_t v___y_3057_; lean_object* v_a_3058_; lean_object* v___y_3060_; lean_object* v___y_3061_; uint8_t v___y_3062_; lean_object* v_a_3063_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v_a_3067_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v_a_3072_; lean_object* v___y_3083_; lean_object* v___y_3084_; uint8_t v_a_3085_; lean_object* v___y_3089_; lean_object* v___y_3090_; uint8_t v___y_3091_; uint8_t v___y_3092_; lean_object* v_a_3093_; lean_object* v___y_3095_; lean_object* v___y_3096_; uint8_t v___y_3097_; lean_object* v_a_3098_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v_a_3103_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; uint8_t v___x_3228_; 
lean_inc(v_name_2913_);
v___f_3030_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3030_, 0, v_name_2913_);
v___x_3031_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1));
v___x_3228_ = lean_unbox(v_a_3026_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; uint8_t v___x_3230_; lean_object* v_a_3232_; lean_object* v_a_3242_; 
v___x_3229_ = l_Lean_trace_profiler;
v___x_3230_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_2917_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3254_; lean_object* v_env_3255_; lean_object* v___x_3256_; 
lean_dec_ref(v___f_3030_);
lean_dec(v_a_3026_);
lean_dec_ref(v___f_2912_);
v___x_3254_ = lean_st_ref_get(v___y_2915_);
v_env_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc_ref(v_env_3255_);
lean_dec(v___x_3254_);
lean_inc(v_name_2913_);
v___x_3256_ = l_Lean_Meta_declFromEqLikeName(v_env_3255_, v_name_2913_);
if (lean_obj_tag(v___x_3256_) == 1)
{
lean_object* v_val_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3330_; 
v_val_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3330_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_val_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3330_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v_fst_3261_; lean_object* v_snd_3262_; lean_object* v___x_3263_; lean_object* v_env_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v_fst_3261_ = lean_ctor_get(v_val_3257_, 0);
lean_inc(v_fst_3261_);
v_snd_3262_ = lean_ctor_get(v_val_3257_, 1);
lean_inc(v_snd_3262_);
lean_dec(v_val_3257_);
v___x_3263_ = lean_st_ref_get(v___y_2915_);
v_env_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_ref(v_env_3264_);
lean_dec(v___x_3263_);
lean_inc(v_snd_3262_);
lean_inc(v_fst_3261_);
v___x_3265_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3264_, v_fst_3261_, v_snd_3262_);
v___x_3266_ = lean_name_eq(v_name_2913_, v___x_3265_);
lean_dec(v___x_3265_);
lean_dec(v_name_2913_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3269_; 
lean_dec(v_snd_3262_);
lean_dec(v_fst_3261_);
lean_del_object(v___x_3028_);
v___x_3267_ = lean_box(v___x_3230_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set_tag(v___x_3259_, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3267_);
v___x_3269_ = v___x_3259_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
else
{
uint8_t v___x_3271_; 
lean_inc(v_snd_3262_);
v___x_3271_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3262_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; uint8_t v___x_3273_; 
lean_del_object(v___x_3028_);
v___x_3272_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3273_ = lean_string_dec_eq(v_snd_3262_, v___x_3272_);
lean_dec(v_snd_3262_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_dec(v_fst_3261_);
v___x_3274_ = lean_box(v___x_3230_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set_tag(v___x_3259_, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3274_);
v___x_3276_ = v___x_3259_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
else
{
uint8_t v___x_3278_; uint8_t v___x_3279_; uint8_t v___x_3280_; lean_object* v___x_3281_; uint64_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_del_object(v___x_3259_);
v___x_3278_ = 1;
v___x_3279_ = 0;
v___x_3280_ = 2;
v___x_3281_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3281_, 0, v___x_3230_);
lean_ctor_set_uint8(v___x_3281_, 1, v___x_3230_);
lean_ctor_set_uint8(v___x_3281_, 2, v___x_3230_);
lean_ctor_set_uint8(v___x_3281_, 3, v___x_3230_);
lean_ctor_set_uint8(v___x_3281_, 4, v___x_3230_);
lean_ctor_set_uint8(v___x_3281_, 5, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 6, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 7, v___x_3230_);
lean_ctor_set_uint8(v___x_3281_, 8, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 9, v___x_3278_);
lean_ctor_set_uint8(v___x_3281_, 10, v___x_3279_);
lean_ctor_set_uint8(v___x_3281_, 11, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 12, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 13, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 14, v___x_3280_);
lean_ctor_set_uint8(v___x_3281_, 15, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 16, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 17, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3281_, 18, v_hasTrace_2918_);
v___x_3282_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set_uint64(v___x_3283_, sizeof(void*)*1, v___x_3282_);
v___x_3284_ = lean_box(1);
v___x_3285_ = lean_unsigned_to_nat(0u);
v___x_3286_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3287_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3288_ = lean_box(0);
v___x_3289_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3289_, 0, v___x_3283_);
lean_ctor_set(v___x_3289_, 1, v___x_3284_);
lean_ctor_set(v___x_3289_, 2, v___x_3286_);
lean_ctor_set(v___x_3289_, 3, v___x_3287_);
lean_ctor_set(v___x_3289_, 4, v___x_3288_);
lean_ctor_set(v___x_3289_, 5, v___x_3285_);
lean_ctor_set(v___x_3289_, 6, v___x_3288_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*7, v___x_3230_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*7 + 1, v___x_3230_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*7 + 2, v___x_3230_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*7 + 3, v_hasTrace_2918_);
v___x_3290_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3291_ = lean_st_mk_ref(v___x_3290_);
v___x_3292_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3261_, v_hasTrace_2918_, v___x_3289_, v___x_3291_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___x_3289_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3294_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3293_);
lean_dec_ref(v___x_3292_);
v___x_3294_ = lean_st_ref_get(v___x_3291_);
lean_dec(v___x_3291_);
lean_dec(v___x_3294_);
v_a_3242_ = v_a_3293_;
goto v___jp_3241_;
}
else
{
lean_dec(v___x_3291_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3295_; 
v_a_3295_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3295_);
lean_dec_ref(v___x_3292_);
v_a_3242_ = v_a_3295_;
goto v___jp_3241_;
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
v_a_3296_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3292_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3292_);
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
}
}
else
{
uint8_t v___x_3304_; uint8_t v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; uint64_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec(v_snd_3262_);
lean_del_object(v___x_3259_);
v___x_3304_ = 1;
v___x_3305_ = 0;
v___x_3306_ = 2;
v___x_3307_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3307_, 0, v___x_3230_);
lean_ctor_set_uint8(v___x_3307_, 1, v___x_3230_);
lean_ctor_set_uint8(v___x_3307_, 2, v___x_3230_);
lean_ctor_set_uint8(v___x_3307_, 3, v___x_3230_);
lean_ctor_set_uint8(v___x_3307_, 4, v___x_3230_);
lean_ctor_set_uint8(v___x_3307_, 5, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 6, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 7, v___x_3230_);
lean_ctor_set_uint8(v___x_3307_, 8, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 9, v___x_3304_);
lean_ctor_set_uint8(v___x_3307_, 10, v___x_3305_);
lean_ctor_set_uint8(v___x_3307_, 11, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 12, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 13, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 14, v___x_3306_);
lean_ctor_set_uint8(v___x_3307_, 15, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 16, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 17, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3307_, 18, v_hasTrace_2918_);
v___x_3308_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3307_);
v___x_3309_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set_uint64(v___x_3309_, sizeof(void*)*1, v___x_3308_);
v___x_3310_ = lean_box(1);
v___x_3311_ = lean_unsigned_to_nat(0u);
v___x_3312_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3314_ = lean_box(0);
v___x_3315_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3315_, 0, v___x_3309_);
lean_ctor_set(v___x_3315_, 1, v___x_3310_);
lean_ctor_set(v___x_3315_, 2, v___x_3312_);
lean_ctor_set(v___x_3315_, 3, v___x_3313_);
lean_ctor_set(v___x_3315_, 4, v___x_3314_);
lean_ctor_set(v___x_3315_, 5, v___x_3311_);
lean_ctor_set(v___x_3315_, 6, v___x_3314_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*7, v___x_3230_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*7 + 1, v___x_3230_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*7 + 2, v___x_3230_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*7 + 3, v_hasTrace_2918_);
v___x_3316_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3317_ = lean_st_mk_ref(v___x_3316_);
v___x_3318_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3261_, v___x_3315_, v___x_3317_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___x_3315_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref(v___x_3318_);
v___x_3320_ = lean_st_ref_get(v___x_3317_);
lean_dec(v___x_3317_);
lean_dec(v___x_3320_);
v_a_3232_ = v_a_3319_;
goto v___jp_3231_;
}
else
{
lean_dec(v___x_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3321_; 
v_a_3321_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3321_);
lean_dec_ref(v___x_3318_);
v_a_3232_ = v_a_3321_;
goto v___jp_3231_;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_del_object(v___x_3028_);
v_a_3322_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3318_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3318_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_dec(v___x_3256_);
lean_del_object(v___x_3028_);
lean_dec(v_name_2913_);
v___x_3331_ = lean_box(v___x_3230_);
v___x_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
return v___x_3332_;
}
}
else
{
lean_del_object(v___x_3028_);
goto v___jp_3112_;
}
v___jp_3231_:
{
if (lean_obj_tag(v_a_3232_) == 0)
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3233_ = lean_box(v___x_3230_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3233_);
v___x_3235_ = v___x_3028_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_dec_ref(v_a_3232_);
v___x_3237_ = lean_box(v_hasTrace_2918_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3237_);
v___x_3239_ = v___x_3028_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
v___jp_3241_:
{
if (lean_obj_tag(v_a_3242_) == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_box(v___x_3230_);
v___x_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
return v___x_3244_;
}
else
{
lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3252_; 
v_isSharedCheck_3252_ = !lean_is_exclusive(v_a_3242_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v_a_3242_, 0);
lean_dec(v_unused_3253_);
v___x_3246_ = v_a_3242_;
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v_a_3242_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3248_ = lean_box(v_hasTrace_2918_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set_tag(v___x_3246_, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3248_);
v___x_3250_ = v___x_3246_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
else
{
lean_del_object(v___x_3028_);
goto v___jp_3112_;
}
v___jp_3032_:
{
lean_object* v___x_3036_; double v___x_3037_; double v___x_3038_; double v___x_3039_; double v___x_3040_; double v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3036_ = lean_io_mono_nanos_now();
v___x_3037_ = lean_float_of_nat(v___y_3034_);
v___x_3038_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3039_ = lean_float_div(v___x_3037_, v___x_3038_);
v___x_3040_ = lean_float_of_nat(v___x_3036_);
v___x_3041_ = lean_float_div(v___x_3040_, v___x_3038_);
v___x_3042_ = lean_box_float(v___x_3039_);
v___x_3043_ = lean_box_float(v___x_3041_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_a_3035_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = lean_unbox(v_a_3026_);
lean_dec(v_a_3026_);
v___x_3047_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v___x_3024_, v_hasTrace_2918_, v___x_3031_, v_options_2917_, v___x_3046_, v___y_3033_, v___f_3030_, v___x_3045_, v___y_2914_, v___y_2915_);
return v___x_3047_;
}
v___jp_3048_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_box(v_a_3051_);
v___x_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
v___y_3033_ = v___y_3049_;
v___y_3034_ = v___y_3050_;
v_a_3035_ = v___x_3053_;
goto v___jp_3032_;
}
v___jp_3054_:
{
if (lean_obj_tag(v_a_3058_) == 0)
{
v___y_3049_ = v___y_3055_;
v___y_3050_ = v___y_3056_;
v_a_3051_ = v___y_3057_;
goto v___jp_3048_;
}
else
{
lean_dec_ref(v_a_3058_);
v___y_3049_ = v___y_3055_;
v___y_3050_ = v___y_3056_;
v_a_3051_ = v_hasTrace_2918_;
goto v___jp_3048_;
}
}
v___jp_3059_:
{
if (lean_obj_tag(v_a_3063_) == 0)
{
v___y_3049_ = v___y_3060_;
v___y_3050_ = v___y_3061_;
v_a_3051_ = v___y_3062_;
goto v___jp_3048_;
}
else
{
lean_dec_ref(v_a_3063_);
v___y_3049_ = v___y_3060_;
v___y_3050_ = v___y_3061_;
v_a_3051_ = v_hasTrace_2918_;
goto v___jp_3048_;
}
}
v___jp_3064_:
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v_a_3067_);
v___y_3033_ = v___y_3065_;
v___y_3034_ = v___y_3066_;
v_a_3035_ = v___x_3068_;
goto v___jp_3032_;
}
v___jp_3069_:
{
lean_object* v___x_3073_; double v___x_3074_; double v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3073_ = lean_io_get_num_heartbeats();
v___x_3074_ = lean_float_of_nat(v___y_3071_);
v___x_3075_ = lean_float_of_nat(v___x_3073_);
v___x_3076_ = lean_box_float(v___x_3074_);
v___x_3077_ = lean_box_float(v___x_3075_);
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v_a_3072_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = lean_unbox(v_a_3026_);
lean_dec(v_a_3026_);
v___x_3081_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v___x_3024_, v_hasTrace_2918_, v___x_3031_, v_options_2917_, v___x_3080_, v___y_3070_, v___f_3030_, v___x_3079_, v___y_2914_, v___y_2915_);
return v___x_3081_;
}
v___jp_3082_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_box(v_a_3085_);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
v___y_3070_ = v___y_3083_;
v___y_3071_ = v___y_3084_;
v_a_3072_ = v___x_3087_;
goto v___jp_3069_;
}
v___jp_3088_:
{
if (lean_obj_tag(v_a_3093_) == 0)
{
v___y_3083_ = v___y_3089_;
v___y_3084_ = v___y_3090_;
v_a_3085_ = v___y_3092_;
goto v___jp_3082_;
}
else
{
lean_dec_ref(v_a_3093_);
v___y_3083_ = v___y_3089_;
v___y_3084_ = v___y_3090_;
v_a_3085_ = v___y_3091_;
goto v___jp_3082_;
}
}
v___jp_3094_:
{
if (lean_obj_tag(v_a_3098_) == 0)
{
uint8_t v___x_3099_; 
v___x_3099_ = 0;
v___y_3083_ = v___y_3095_;
v___y_3084_ = v___y_3096_;
v_a_3085_ = v___x_3099_;
goto v___jp_3082_;
}
else
{
lean_dec_ref(v_a_3098_);
v___y_3083_ = v___y_3095_;
v___y_3084_ = v___y_3096_;
v_a_3085_ = v___y_3097_;
goto v___jp_3082_;
}
}
v___jp_3100_:
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_a_3103_);
v___y_3070_ = v___y_3101_;
v___y_3071_ = v___y_3102_;
v_a_3072_ = v___x_3104_;
goto v___jp_3069_;
}
v___jp_3105_:
{
if (lean_obj_tag(v___y_3108_) == 0)
{
lean_object* v_a_3109_; uint8_t v___x_3110_; 
v_a_3109_ = lean_ctor_get(v___y_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref(v___y_3108_);
v___x_3110_ = lean_unbox(v_a_3109_);
lean_dec(v_a_3109_);
v___y_3083_ = v___y_3106_;
v___y_3084_ = v___y_3107_;
v_a_3085_ = v___x_3110_;
goto v___jp_3082_;
}
else
{
lean_object* v_a_3111_; 
v_a_3111_ = lean_ctor_get(v___y_3108_, 0);
lean_inc(v_a_3111_);
lean_dec_ref(v___y_3108_);
v___y_3101_ = v___y_3106_;
v___y_3102_ = v___y_3107_;
v_a_3103_ = v_a_3111_;
goto v___jp_3100_;
}
}
v___jp_3112_:
{
lean_object* v___x_3113_; lean_object* v_a_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3113_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_2915_);
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref(v___x_3113_);
v___x_3115_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3116_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_2917_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_env_3119_; lean_object* v___x_3120_; 
lean_dec_ref(v___f_2912_);
v___x_3117_ = lean_io_mono_nanos_now();
v___x_3118_ = lean_st_ref_get(v___y_2915_);
v_env_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc_ref(v_env_3119_);
lean_dec(v___x_3118_);
lean_inc(v_name_2913_);
v___x_3120_ = l_Lean_Meta_declFromEqLikeName(v_env_3119_, v_name_2913_);
if (lean_obj_tag(v___x_3120_) == 1)
{
lean_object* v_val_3121_; lean_object* v_fst_3122_; lean_object* v_snd_3123_; lean_object* v___x_3124_; lean_object* v_env_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v_val_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_val_3121_);
lean_dec_ref(v___x_3120_);
v_fst_3122_ = lean_ctor_get(v_val_3121_, 0);
lean_inc(v_fst_3122_);
v_snd_3123_ = lean_ctor_get(v_val_3121_, 1);
lean_inc(v_snd_3123_);
lean_dec(v_val_3121_);
v___x_3124_ = lean_st_ref_get(v___y_2915_);
v_env_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc_ref(v_env_3125_);
lean_dec(v___x_3124_);
lean_inc(v_snd_3123_);
lean_inc(v_fst_3122_);
v___x_3126_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3125_, v_fst_3122_, v_snd_3123_);
v___x_3127_ = lean_name_eq(v_name_2913_, v___x_3126_);
lean_dec(v___x_3126_);
lean_dec(v_name_2913_);
if (v___x_3127_ == 0)
{
lean_dec(v_snd_3123_);
lean_dec(v_fst_3122_);
v___y_3049_ = v_a_3114_;
v___y_3050_ = v___x_3117_;
v_a_3051_ = v___x_3116_;
goto v___jp_3048_;
}
else
{
uint8_t v___x_3128_; 
lean_inc(v_snd_3123_);
v___x_3128_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3123_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3130_ = lean_string_dec_eq(v_snd_3123_, v___x_3129_);
lean_dec(v_snd_3123_);
if (v___x_3130_ == 0)
{
lean_dec(v_fst_3122_);
v___y_3049_ = v_a_3114_;
v___y_3050_ = v___x_3117_;
v_a_3051_ = v___x_3116_;
goto v___jp_3048_;
}
else
{
uint8_t v___x_3131_; uint8_t v___x_3132_; uint8_t v___x_3133_; lean_object* v___x_3134_; uint64_t v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3131_ = 1;
v___x_3132_ = 0;
v___x_3133_ = 2;
v___x_3134_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3134_, 0, v___x_3116_);
lean_ctor_set_uint8(v___x_3134_, 1, v___x_3116_);
lean_ctor_set_uint8(v___x_3134_, 2, v___x_3116_);
lean_ctor_set_uint8(v___x_3134_, 3, v___x_3116_);
lean_ctor_set_uint8(v___x_3134_, 4, v___x_3116_);
lean_ctor_set_uint8(v___x_3134_, 5, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 6, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 7, v___x_3116_);
lean_ctor_set_uint8(v___x_3134_, 8, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 9, v___x_3131_);
lean_ctor_set_uint8(v___x_3134_, 10, v___x_3132_);
lean_ctor_set_uint8(v___x_3134_, 11, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 12, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 13, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 14, v___x_3133_);
lean_ctor_set_uint8(v___x_3134_, 15, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 16, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 17, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3134_, 18, v_hasTrace_2918_);
v___x_3135_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3134_);
v___x_3136_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set_uint64(v___x_3136_, sizeof(void*)*1, v___x_3135_);
v___x_3137_ = lean_box(1);
v___x_3138_ = lean_unsigned_to_nat(0u);
v___x_3139_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3140_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3142_, 0, v___x_3136_);
lean_ctor_set(v___x_3142_, 1, v___x_3137_);
lean_ctor_set(v___x_3142_, 2, v___x_3139_);
lean_ctor_set(v___x_3142_, 3, v___x_3140_);
lean_ctor_set(v___x_3142_, 4, v___x_3141_);
lean_ctor_set(v___x_3142_, 5, v___x_3138_);
lean_ctor_set(v___x_3142_, 6, v___x_3141_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*7, v___x_3116_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*7 + 1, v___x_3116_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*7 + 2, v___x_3116_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*7 + 3, v_hasTrace_2918_);
v___x_3143_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3144_ = lean_st_mk_ref(v___x_3143_);
v___x_3145_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3122_, v_hasTrace_2918_, v___x_3142_, v___x_3144_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___x_3142_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3147_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref(v___x_3145_);
v___x_3147_ = lean_st_ref_get(v___x_3144_);
lean_dec(v___x_3144_);
lean_dec(v___x_3147_);
v___y_3060_ = v_a_3114_;
v___y_3061_ = v___x_3117_;
v___y_3062_ = v___x_3116_;
v_a_3063_ = v_a_3146_;
goto v___jp_3059_;
}
else
{
lean_dec(v___x_3144_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3148_; 
v_a_3148_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3148_);
lean_dec_ref(v___x_3145_);
v___y_3060_ = v_a_3114_;
v___y_3061_ = v___x_3117_;
v___y_3062_ = v___x_3116_;
v_a_3063_ = v_a_3148_;
goto v___jp_3059_;
}
else
{
lean_object* v_a_3149_; 
v_a_3149_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3149_);
lean_dec_ref(v___x_3145_);
v___y_3065_ = v_a_3114_;
v___y_3066_ = v___x_3117_;
v_a_3067_ = v_a_3149_;
goto v___jp_3064_;
}
}
}
}
else
{
uint8_t v___x_3150_; uint8_t v___x_3151_; uint8_t v___x_3152_; lean_object* v___x_3153_; uint64_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
lean_dec(v_snd_3123_);
v___x_3150_ = 1;
v___x_3151_ = 0;
v___x_3152_ = 2;
v___x_3153_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3153_, 0, v___x_3116_);
lean_ctor_set_uint8(v___x_3153_, 1, v___x_3116_);
lean_ctor_set_uint8(v___x_3153_, 2, v___x_3116_);
lean_ctor_set_uint8(v___x_3153_, 3, v___x_3116_);
lean_ctor_set_uint8(v___x_3153_, 4, v___x_3116_);
lean_ctor_set_uint8(v___x_3153_, 5, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 6, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 7, v___x_3116_);
lean_ctor_set_uint8(v___x_3153_, 8, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 9, v___x_3150_);
lean_ctor_set_uint8(v___x_3153_, 10, v___x_3151_);
lean_ctor_set_uint8(v___x_3153_, 11, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 12, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 13, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 14, v___x_3152_);
lean_ctor_set_uint8(v___x_3153_, 15, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 16, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 17, v_hasTrace_2918_);
lean_ctor_set_uint8(v___x_3153_, 18, v_hasTrace_2918_);
v___x_3154_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3155_, 0, v___x_3153_);
lean_ctor_set_uint64(v___x_3155_, sizeof(void*)*1, v___x_3154_);
v___x_3156_ = lean_box(1);
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3159_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3160_ = lean_box(0);
v___x_3161_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3161_, 0, v___x_3155_);
lean_ctor_set(v___x_3161_, 1, v___x_3156_);
lean_ctor_set(v___x_3161_, 2, v___x_3158_);
lean_ctor_set(v___x_3161_, 3, v___x_3159_);
lean_ctor_set(v___x_3161_, 4, v___x_3160_);
lean_ctor_set(v___x_3161_, 5, v___x_3157_);
lean_ctor_set(v___x_3161_, 6, v___x_3160_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*7, v___x_3116_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*7 + 1, v___x_3116_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*7 + 2, v___x_3116_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*7 + 3, v_hasTrace_2918_);
v___x_3162_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3163_ = lean_st_mk_ref(v___x_3162_);
v___x_3164_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3122_, v___x_3161_, v___x_3163_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___x_3161_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = lean_st_ref_get(v___x_3163_);
lean_dec(v___x_3163_);
lean_dec(v___x_3166_);
v___y_3055_ = v_a_3114_;
v___y_3056_ = v___x_3117_;
v___y_3057_ = v___x_3116_;
v_a_3058_ = v_a_3165_;
goto v___jp_3054_;
}
else
{
lean_dec(v___x_3163_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3167_; 
v_a_3167_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3167_);
lean_dec_ref(v___x_3164_);
v___y_3055_ = v_a_3114_;
v___y_3056_ = v___x_3117_;
v___y_3057_ = v___x_3116_;
v_a_3058_ = v_a_3167_;
goto v___jp_3054_;
}
else
{
lean_object* v_a_3168_; 
v_a_3168_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3168_);
lean_dec_ref(v___x_3164_);
v___y_3065_ = v_a_3114_;
v___y_3066_ = v___x_3117_;
v_a_3067_ = v_a_3168_;
goto v___jp_3064_;
}
}
}
}
}
else
{
lean_dec(v___x_3120_);
lean_dec(v_name_2913_);
v___y_3049_ = v_a_3114_;
v___y_3050_ = v___x_3117_;
v_a_3051_ = v___x_3116_;
goto v___jp_3048_;
}
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v_env_3171_; lean_object* v___x_3172_; 
v___x_3169_ = lean_io_get_num_heartbeats();
v___x_3170_ = lean_st_ref_get(v___y_2915_);
v_env_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc_ref(v_env_3171_);
lean_dec(v___x_3170_);
lean_inc(v_name_2913_);
v___x_3172_ = l_Lean_Meta_declFromEqLikeName(v_env_3171_, v_name_2913_);
if (lean_obj_tag(v___x_3172_) == 1)
{
lean_object* v_val_3173_; lean_object* v_fst_3174_; lean_object* v_snd_3175_; lean_object* v___x_3176_; lean_object* v_env_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v_val_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_val_3173_);
lean_dec_ref(v___x_3172_);
v_fst_3174_ = lean_ctor_get(v_val_3173_, 0);
lean_inc(v_fst_3174_);
v_snd_3175_ = lean_ctor_get(v_val_3173_, 1);
lean_inc(v_snd_3175_);
lean_dec(v_val_3173_);
v___x_3176_ = lean_st_ref_get(v___y_2915_);
v_env_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc_ref(v_env_3177_);
lean_dec(v___x_3176_);
lean_inc(v_snd_3175_);
lean_inc(v_fst_3174_);
v___x_3178_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3177_, v_fst_3174_, v_snd_3175_);
v___x_3179_ = lean_name_eq(v_name_2913_, v___x_3178_);
lean_dec(v___x_3178_);
lean_dec(v_name_2913_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_dec(v_snd_3175_);
lean_dec(v_fst_3174_);
v___x_3180_ = lean_box(0);
lean_inc(v___y_2915_);
lean_inc_ref(v___y_2914_);
v___x_3181_ = lean_apply_4(v___f_2912_, v___x_3180_, v___y_2914_, v___y_2915_, lean_box(0));
v___y_3106_ = v_a_3114_;
v___y_3107_ = v___x_3169_;
v___y_3108_ = v___x_3181_;
goto v___jp_3105_;
}
else
{
uint8_t v___x_3182_; 
lean_inc(v_snd_3175_);
v___x_3182_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3175_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3184_ = lean_string_dec_eq(v_snd_3175_, v___x_3183_);
lean_dec(v_snd_3175_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v_fst_3174_);
v___x_3185_ = lean_box(0);
lean_inc(v___y_2915_);
lean_inc_ref(v___y_2914_);
v___x_3186_ = lean_apply_4(v___f_2912_, v___x_3185_, v___y_2914_, v___y_2915_, lean_box(0));
v___y_3106_ = v_a_3114_;
v___y_3107_ = v___x_3169_;
v___y_3108_ = v___x_3186_;
goto v___jp_3105_;
}
else
{
uint8_t v___x_3187_; uint8_t v___x_3188_; uint8_t v___x_3189_; lean_object* v___x_3190_; uint64_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_dec_ref(v___f_2912_);
v___x_3187_ = 1;
v___x_3188_ = 0;
v___x_3189_ = 2;
v___x_3190_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3190_, 0, v___x_3182_);
lean_ctor_set_uint8(v___x_3190_, 1, v___x_3182_);
lean_ctor_set_uint8(v___x_3190_, 2, v___x_3182_);
lean_ctor_set_uint8(v___x_3190_, 3, v___x_3182_);
lean_ctor_set_uint8(v___x_3190_, 4, v___x_3182_);
lean_ctor_set_uint8(v___x_3190_, 5, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 6, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 7, v___x_3182_);
lean_ctor_set_uint8(v___x_3190_, 8, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 9, v___x_3187_);
lean_ctor_set_uint8(v___x_3190_, 10, v___x_3188_);
lean_ctor_set_uint8(v___x_3190_, 11, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 12, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 13, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 14, v___x_3189_);
lean_ctor_set_uint8(v___x_3190_, 15, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 16, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 17, v___x_3116_);
lean_ctor_set_uint8(v___x_3190_, 18, v___x_3116_);
v___x_3191_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3190_);
v___x_3192_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set_uint64(v___x_3192_, sizeof(void*)*1, v___x_3191_);
v___x_3193_ = lean_box(1);
v___x_3194_ = lean_unsigned_to_nat(0u);
v___x_3195_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3196_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3197_ = lean_box(0);
v___x_3198_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3198_, 0, v___x_3192_);
lean_ctor_set(v___x_3198_, 1, v___x_3193_);
lean_ctor_set(v___x_3198_, 2, v___x_3195_);
lean_ctor_set(v___x_3198_, 3, v___x_3196_);
lean_ctor_set(v___x_3198_, 4, v___x_3197_);
lean_ctor_set(v___x_3198_, 5, v___x_3194_);
lean_ctor_set(v___x_3198_, 6, v___x_3197_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*7, v___x_3182_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*7 + 1, v___x_3182_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*7 + 2, v___x_3182_);
lean_ctor_set_uint8(v___x_3198_, sizeof(void*)*7 + 3, v___x_3116_);
v___x_3199_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3200_ = lean_st_mk_ref(v___x_3199_);
v___x_3201_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3174_, v___x_3116_, v___x_3198_, v___x_3200_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___x_3198_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3203_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref(v___x_3201_);
v___x_3203_ = lean_st_ref_get(v___x_3200_);
lean_dec(v___x_3200_);
lean_dec(v___x_3203_);
v___y_3089_ = v_a_3114_;
v___y_3090_ = v___x_3169_;
v___y_3091_ = v___x_3116_;
v___y_3092_ = v___x_3182_;
v_a_3093_ = v_a_3202_;
goto v___jp_3088_;
}
else
{
lean_dec(v___x_3200_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3204_; 
v_a_3204_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3204_);
lean_dec_ref(v___x_3201_);
v___y_3089_ = v_a_3114_;
v___y_3090_ = v___x_3169_;
v___y_3091_ = v___x_3116_;
v___y_3092_ = v___x_3182_;
v_a_3093_ = v_a_3204_;
goto v___jp_3088_;
}
else
{
lean_object* v_a_3205_; 
v_a_3205_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3201_);
v___y_3101_ = v_a_3114_;
v___y_3102_ = v___x_3169_;
v_a_3103_ = v_a_3205_;
goto v___jp_3100_;
}
}
}
}
else
{
uint8_t v___x_3206_; uint8_t v___x_3207_; uint8_t v___x_3208_; uint8_t v___x_3209_; lean_object* v___x_3210_; uint64_t v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec(v_snd_3175_);
lean_dec_ref(v___f_2912_);
v___x_3206_ = 0;
v___x_3207_ = 1;
v___x_3208_ = 0;
v___x_3209_ = 2;
v___x_3210_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3210_, 0, v___x_3206_);
lean_ctor_set_uint8(v___x_3210_, 1, v___x_3206_);
lean_ctor_set_uint8(v___x_3210_, 2, v___x_3206_);
lean_ctor_set_uint8(v___x_3210_, 3, v___x_3206_);
lean_ctor_set_uint8(v___x_3210_, 4, v___x_3206_);
lean_ctor_set_uint8(v___x_3210_, 5, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 6, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 7, v___x_3206_);
lean_ctor_set_uint8(v___x_3210_, 8, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 9, v___x_3207_);
lean_ctor_set_uint8(v___x_3210_, 10, v___x_3208_);
lean_ctor_set_uint8(v___x_3210_, 11, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 12, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 13, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 14, v___x_3209_);
lean_ctor_set_uint8(v___x_3210_, 15, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 16, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 17, v___x_3116_);
lean_ctor_set_uint8(v___x_3210_, 18, v___x_3116_);
v___x_3211_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set_uint64(v___x_3212_, sizeof(void*)*1, v___x_3211_);
v___x_3213_ = lean_box(1);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3216_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3217_ = lean_box(0);
v___x_3218_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3218_, 0, v___x_3212_);
lean_ctor_set(v___x_3218_, 1, v___x_3213_);
lean_ctor_set(v___x_3218_, 2, v___x_3215_);
lean_ctor_set(v___x_3218_, 3, v___x_3216_);
lean_ctor_set(v___x_3218_, 4, v___x_3217_);
lean_ctor_set(v___x_3218_, 5, v___x_3214_);
lean_ctor_set(v___x_3218_, 6, v___x_3217_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*7, v___x_3206_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*7 + 1, v___x_3206_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*7 + 2, v___x_3206_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*7 + 3, v___x_3116_);
v___x_3219_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3220_ = lean_st_mk_ref(v___x_3219_);
v___x_3221_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3174_, v___x_3218_, v___x_3220_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___x_3218_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3223_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref(v___x_3221_);
v___x_3223_ = lean_st_ref_get(v___x_3220_);
lean_dec(v___x_3220_);
lean_dec(v___x_3223_);
v___y_3095_ = v_a_3114_;
v___y_3096_ = v___x_3169_;
v___y_3097_ = v___x_3116_;
v_a_3098_ = v_a_3222_;
goto v___jp_3094_;
}
else
{
lean_dec(v___x_3220_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3224_; 
v_a_3224_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3224_);
lean_dec_ref(v___x_3221_);
v___y_3095_ = v_a_3114_;
v___y_3096_ = v___x_3169_;
v___y_3097_ = v___x_3116_;
v_a_3098_ = v_a_3224_;
goto v___jp_3094_;
}
else
{
lean_object* v_a_3225_; 
v_a_3225_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3225_);
lean_dec_ref(v___x_3221_);
v___y_3101_ = v_a_3114_;
v___y_3102_ = v___x_3169_;
v_a_3103_ = v_a_3225_;
goto v___jp_3100_;
}
}
}
}
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec(v___x_3172_);
lean_dec(v_name_2913_);
v___x_3226_ = lean_box(0);
lean_inc(v___y_2915_);
lean_inc_ref(v___y_2914_);
v___x_3227_ = lean_apply_4(v___f_2912_, v___x_3226_, v___y_2914_, v___y_2915_, lean_box(0));
v___y_3106_ = v_a_3114_;
v___y_3107_ = v___x_3169_;
v___y_3108_ = v___x_3227_;
goto v___jp_3105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3334_, lean_object* v_name_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3334_, v_name_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
return v_res_3339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_unsigned_to_nat(3137104340u);
v___x_3384_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3385_ = l_Lean_Name_num___override(v___x_3384_, v___x_3383_);
return v___x_3385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3388_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3389_ = l_Lean_Name_str___override(v___x_3388_, v___x_3387_);
return v___x_3389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3392_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3393_ = l_Lean_Name_str___override(v___x_3392_, v___x_3391_);
return v___x_3393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = lean_unsigned_to_nat(2u);
v___x_3395_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3396_ = l_Lean_Name_num___override(v___x_3395_, v___x_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3398_; lean_object* v___x_3399_; 
v___f_3398_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3399_ = l_Lean_registerReservedNameAction(v___f_3398_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v___x_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v___x_3399_);
v___x_3400_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_3401_ = 0;
v___x_3402_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3403_ = l_Lean_registerTraceClass(v___x_3400_, v___x_3401_, v___x_3402_);
return v___x_3403_;
}
else
{
return v___x_3399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_00_u03b1_3406_, lean_object* v_x_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_x_3407_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_00_u03b1_3412_, lean_object* v_x_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4(v_00_u03b1_3412_, v_x_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3417_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_RecExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LetToHave(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_RecExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2238725263____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_eqns_nonrecursive = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_eqns_nonrecursive);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_2608443134____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_eqns_deepRecursiveSplit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_eqns_deepRecursiveSplit);
lean_dec_ref(res);
l_Lean_Meta_eqnAffectingOptions = _init_l_Lean_Meta_eqnAffectingOptions();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions);
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef);
lean_dec_ref(res);
l_Lean_Meta_instInhabitedEqnsExtState_default = _init_l_Lean_Meta_instInhabitedEqnsExtState_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedEqnsExtState_default);
l_Lean_Meta_instInhabitedEqnsExtState = _init_l_Lean_Meta_instInhabitedEqnsExtState();
lean_mark_persistent(l_Lean_Meta_instInhabitedEqnsExtState);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_eqnsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_eqnsExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin);
lean_object* initialize_Lean_Meta_RecExt(uint8_t builtin);
lean_object* initialize_Lean_Meta_LetToHave(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Eqns(builtin);
}
#ifdef __cplusplus
}
#endif
