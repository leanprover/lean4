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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_generateEagerEqns___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_generateEagerEqns___closed__4;
static const lean_string_object l_Lean_Meta_generateEagerEqns___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "generating eager equations for "};
static const lean_object* l_Lean_Meta_generateEagerEqns___closed__5 = (const lean_object*)&l_Lean_Meta_generateEagerEqns___closed__5_value;
static lean_once_cell_t l_Lean_Meta_generateEagerEqns___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_generateEagerEqns___closed__6;
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Eqns reserved name action for "};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_b_140_);
return v_b_140_;
}
else
{
lean_object* v_head_141_; lean_object* v_tail_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_162_; 
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_163_, lean_object* v_env_164_, lean_object* v_as_x27_165_, lean_object* v_b_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_163_, v_env_164_, v_as_x27_165_, v_b_166_);
lean_dec_ref(v_b_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_168_, lean_object* v_name_169_){
_start:
{
if (lean_obj_tag(v_name_169_) == 1)
{
lean_object* v_pre_170_; lean_object* v_str_171_; uint8_t v___x_172_; 
v_pre_170_ = lean_ctor_get(v_name_169_, 0);
lean_inc(v_pre_170_);
v_str_171_ = lean_ctor_get(v_name_169_, 1);
lean_inc_ref_n(v_str_171_, 2);
lean_dec_ref(v_name_169_);
v___x_172_ = l_Lean_Meta_isEqnLikeSuffix(v_str_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_dec_ref(v_str_171_);
lean_dec(v_pre_170_);
lean_dec_ref(v_env_168_);
v___x_173_ = lean_box(0);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_fst_181_; 
lean_inc(v_pre_170_);
v___x_174_ = l_Lean_privateToUserName(v_pre_170_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v_pre_170_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_box(0);
v___x_179_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_180_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_171_, v_env_168_, v___x_177_, v___x_179_);
v_fst_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_fst_181_);
lean_dec_ref(v___x_180_);
if (lean_obj_tag(v_fst_181_) == 0)
{
return v___x_178_;
}
else
{
lean_object* v_val_182_; 
v_val_182_ = lean_ctor_get(v_fst_181_, 0);
lean_inc(v_val_182_);
lean_dec_ref(v_fst_181_);
return v_val_182_;
}
}
}
else
{
lean_object* v___x_183_; 
lean_dec(v_name_169_);
lean_dec_ref(v_env_168_);
v___x_183_ = lean_box(0);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_184_, lean_object* v_env_185_, lean_object* v_as_186_, lean_object* v_as_x27_187_, lean_object* v_b_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_184_, v_env_185_, v_as_x27_187_, v_b_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_191_, lean_object* v_env_192_, lean_object* v_as_193_, lean_object* v_as_x27_194_, lean_object* v_b_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_191_, v_env_192_, v_as_193_, v_as_x27_194_, v_b_195_, v_a_196_);
lean_dec_ref(v_b_195_);
lean_dec(v_as_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_198_, lean_object* v_declName_199_, lean_object* v_suffix_200_){
_start:
{
lean_object* v___x_204_; uint8_t v_isModule_205_; 
v___x_204_ = l_Lean_Environment_header(v_env_198_);
v_isModule_205_ = lean_ctor_get_uint8(v___x_204_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_204_);
if (v_isModule_205_ == 0)
{
lean_object* v_name_206_; 
lean_dec_ref(v_env_198_);
v_name_206_ = l_Lean_Name_str___override(v_declName_199_, v_suffix_200_);
return v_name_206_;
}
else
{
uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = 0;
lean_inc_ref(v_env_198_);
v___x_208_ = l_Lean_Environment_setExporting(v_env_198_, v_isModule_205_);
lean_inc(v_declName_199_);
v___x_209_ = l_Lean_Environment_find_x3f(v___x_208_, v_declName_199_, v___x_207_);
if (lean_obj_tag(v___x_209_) == 0)
{
goto v___jp_201_;
}
else
{
lean_object* v_val_210_; uint8_t v___x_211_; 
v_val_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = l_Lean_ConstantInfo_hasValue(v_val_210_, v___x_207_);
lean_dec(v_val_210_);
if (v___x_211_ == 0)
{
goto v___jp_201_;
}
else
{
lean_object* v_name_212_; 
lean_dec_ref(v_env_198_);
v_name_212_ = l_Lean_Name_str___override(v_declName_199_, v_suffix_200_);
return v_name_212_;
}
}
}
v___jp_201_:
{
lean_object* v_name_202_; lean_object* v___x_203_; 
v_name_202_ = l_Lean_Name_str___override(v_declName_199_, v_suffix_200_);
v___x_203_ = l_Lean_mkPrivateName(v_env_198_, v_name_202_);
lean_dec_ref(v_env_198_);
return v___x_203_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_213_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
lean_ctor_set(v___x_218_, 2, v___x_217_);
lean_ctor_set(v___x_218_, 3, v___x_217_);
lean_ctor_set(v___x_218_, 4, v___x_216_);
lean_ctor_set(v___x_218_, 5, v___x_216_);
lean_ctor_set(v___x_218_, 6, v___x_216_);
lean_ctor_set(v___x_218_, 7, v___x_216_);
lean_ctor_set(v___x_218_, 8, v___x_216_);
lean_ctor_set(v___x_218_, 9, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(32u);
v___x_220_ = lean_mk_empty_array_with_capacity(v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_222_ = ((size_t)5ULL);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_unsigned_to_nat(32u);
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_224_);
v___x_226_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_227_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_223_);
lean_ctor_set(v___x_227_, 3, v___x_223_);
lean_ctor_set_usize(v___x_227_, 4, v___x_222_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_box(1);
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_228_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; lean_object* v_env_237_; lean_object* v_options_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_236_ = lean_st_ref_get(v___y_234_);
v_env_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_env_237_);
lean_dec(v___x_236_);
v_options_238_ = lean_ctor_get(v___y_233_, 2);
v___x_239_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_240_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_238_);
v___x_241_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_241_, 0, v_env_237_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
lean_ctor_set(v___x_241_, 3, v_options_238_);
v___x_242_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_msgData_232_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_ref_253_; lean_object* v___x_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_ref_253_ = lean_ctor_get(v___y_250_, 5);
v___x_254_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_249_, v___y_250_, v___y_251_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_inc(v_ref_253_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_ref_253_);
lean_ctor_set(v___x_259_, 1, v_a_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_268_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_271_ = l_Lean_stringToMessageData(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_277_ = l_Lean_stringToMessageData(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_278_, lean_object* v_reservedName_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_283_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_284_ = 0;
v___x_285_ = l_Lean_MessageData_ofConstName(v_declName_278_, v___x_284_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_283_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = 1;
v___x_290_ = l_Lean_MessageData_ofConstName(v_reservedName_279_, v___x_289_);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_288_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_293_, v___y_280_, v___y_281_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_295_, lean_object* v_reservedName_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_295_, v_reservedName_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_301_, lean_object* v_suffix_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_env_307_; lean_object* v_reservedName_308_; uint8_t v___x_309_; uint8_t v___x_310_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_306_);
lean_inc(v_declName_301_);
v_reservedName_308_ = l_Lean_Name_str___override(v_declName_301_, v_suffix_302_);
v___x_309_ = 1;
lean_inc(v_reservedName_308_);
v___x_310_ = l_Lean_Environment_contains(v_env_307_, v_reservedName_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_reservedName_308_);
lean_dec(v_declName_301_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_301_, v_reservedName_308_, v___y_303_, v___y_304_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_314_, lean_object* v_suffix_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_314_, v_suffix_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_320_);
v___x_325_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_320_, v___x_324_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec_ref(v___x_325_);
v___x_326_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_320_);
v___x_327_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_320_, v___x_326_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v___x_327_);
v___x_328_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_329_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_320_, v___x_328_, v_a_321_, v_a_322_);
return v___x_329_;
}
else
{
lean_dec(v_declName_320_);
return v___x_327_;
}
}
else
{
lean_dec(v_declName_320_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_335_, lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_336_, v___y_337_, v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_341_, v_msg_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_347_, lean_object* v_n_348_){
_start:
{
lean_object* v___x_349_; 
lean_inc(v_n_348_);
lean_inc_ref(v_env_347_);
v___x_349_ = l_Lean_Meta_declFromEqLikeName(v_env_347_, v_n_348_);
if (lean_obj_tag(v___x_349_) == 1)
{
lean_object* v_val_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_val_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_val_350_);
lean_dec_ref(v___x_349_);
v_fst_351_ = lean_ctor_get(v_val_350_, 0);
lean_inc(v_fst_351_);
v_snd_352_ = lean_ctor_get(v_val_350_, 1);
lean_inc(v_snd_352_);
lean_dec(v_val_350_);
v___x_353_ = l_Lean_Meta_mkEqLikeNameFor(v_env_347_, v_fst_351_, v_snd_352_);
v___x_354_ = lean_name_eq(v_n_348_, v___x_353_);
lean_dec(v___x_353_);
lean_dec(v_n_348_);
return v___x_354_;
}
else
{
uint8_t v___x_355_; 
lean_dec(v___x_349_);
lean_dec(v_n_348_);
lean_dec_ref(v_env_347_);
v___x_355_ = 0;
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_356_, lean_object* v_n_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_356_, v_n_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_362_; lean_object* v___x_363_; 
v___f_362_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_363_ = l_Lean_registerReservedNamePredicate(v___f_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_box(0);
v___x_368_ = lean_st_mk_ref(v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_374_ = lean_mk_io_user_error(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_initializing();
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_394_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_394_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_unbox(v_a_378_);
lean_dec(v_a_378_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
lean_dec_ref(v_f_375_);
v___x_383_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
lean_ctor_set(v___x_380_, 0, v___x_383_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_387_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_388_ = lean_st_ref_take(v___x_387_);
v___x_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_389_, 0, v_f_375_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_st_ref_set(v___x_387_, v___x_389_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_390_);
v___x_392_ = v___x_380_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_f_375_);
v_a_395_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_377_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_377_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_registerGetEqnsFn(v_f_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_416_; lean_object* v_env_417_; uint8_t v___x_418_; lean_object* v___x_419_; 
v___x_416_ = lean_st_ref_get(v_a_410_);
v_env_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc_ref(v_env_417_);
lean_dec(v___x_416_);
v___x_418_ = 0;
lean_inc(v_declName_406_);
v___x_419_ = l_Lean_Environment_findAsync_x3f(v_env_417_, v_declName_406_, v___x_418_);
if (lean_obj_tag(v___x_419_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_451_; 
v_val_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_451_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_451_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_val_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_451_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
uint8_t v_kind_424_; 
v_kind_424_ = lean_ctor_get_uint8(v_val_420_, sizeof(void*)*3);
if (v_kind_424_ == 0)
{
lean_object* v_sig_425_; lean_object* v___x_426_; lean_object* v_env_427_; uint8_t v___x_428_; 
v_sig_425_ = lean_ctor_get(v_val_420_, 1);
lean_inc_ref(v_sig_425_);
lean_dec(v_val_420_);
v___x_426_ = lean_st_ref_get(v_a_410_);
v_env_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_env_427_);
lean_dec(v___x_426_);
v___x_428_ = lean_is_matcher(v_env_427_, v_declName_406_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v_type_430_; lean_object* v___x_431_; 
lean_del_object(v___x_422_);
v___x_429_ = lean_task_get_own(v_sig_425_);
v_type_430_ = lean_ctor_get(v___x_429_, 2);
lean_inc_ref(v_type_430_);
lean_dec(v___x_429_);
v___x_431_ = l_Lean_Meta_isProp(v_type_430_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_446_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_446_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_446_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_446_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v___x_436_; 
v___x_436_ = lean_unbox(v_a_432_);
lean_dec(v_a_432_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_437_ = 1;
v___x_438_ = lean_box(v___x_437_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_438_);
v___x_440_ = v___x_434_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_box(v___x_428_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_442_);
v___x_444_ = v___x_434_;
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
}
else
{
return v___x_431_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_449_; 
lean_dec_ref(v_sig_425_);
v___x_447_ = lean_box(v___x_418_);
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 0);
lean_ctor_set(v___x_422_, 0, v___x_447_);
v___x_449_ = v___x_422_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_del_object(v___x_422_);
lean_dec(v_val_420_);
lean_dec(v_declName_406_);
goto v___jp_412_;
}
}
}
else
{
lean_dec(v___x_419_);
lean_dec(v_declName_406_);
goto v___jp_412_;
}
v___jp_412_:
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = 0;
v___x_414_ = lean_box(v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
return v_res_458_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_467_);
return v_res_469_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_470_; lean_object* v___f_471_; 
v___x_470_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_471_ = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_471_, 0, v___x_470_);
return v___f_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___f_473_ = lean_obj_once(&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_474_ = lean_box(0);
v___x_475_ = lean_box(1);
v___x_476_ = l_Lean_registerEnvExtension___redArg(v___f_473_, v___x_474_, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; lean_object* v_env_483_; lean_object* v_toConstantVal_484_; lean_object* v_value_485_; lean_object* v_all_486_; uint8_t v___y_488_; lean_object* v_type_496_; uint8_t v___x_497_; 
v___x_482_ = lean_st_ref_get(v___y_480_);
v_env_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_ref_n(v_env_483_, 2);
lean_dec(v___x_482_);
v_toConstantVal_484_ = lean_ctor_get(v_thm_479_, 0);
v_value_485_ = lean_ctor_get(v_thm_479_, 1);
v_all_486_ = lean_ctor_get(v_thm_479_, 2);
v_type_496_ = lean_ctor_get(v_toConstantVal_484_, 2);
v___x_497_ = l_Lean_Environment_hasUnsafe(v_env_483_, v_type_496_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
v___x_498_ = l_Lean_Environment_hasUnsafe(v_env_483_, v_value_485_);
v___y_488_ = v___x_498_;
goto v___jp_487_;
}
else
{
lean_dec_ref(v_env_483_);
v___y_488_ = v___x_497_;
goto v___jp_487_;
}
v___jp_487_:
{
if (v___y_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_489_, 0, v_thm_479_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_inc(v_all_486_);
lean_inc_ref(v_value_485_);
lean_inc_ref(v_toConstantVal_484_);
lean_dec_ref(v_thm_479_);
v___x_491_ = lean_box(0);
v___x_492_ = 0;
v___x_493_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_493_, 0, v_toConstantVal_484_);
lean_ctor_set(v___x_493_, 1, v_value_485_);
lean_ctor_set(v___x_493_, 2, v___x_491_);
lean_ctor_set(v___x_493_, 3, v_all_486_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*4, v___x_492_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_499_, v___y_500_);
lean_dec(v___y_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_503_, v___y_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_517_, lean_object* v_b_518_, lean_object* v_c_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
lean_inc(v___y_523_);
lean_inc_ref(v___y_522_);
lean_inc(v___y_521_);
lean_inc_ref(v___y_520_);
v___x_525_ = lean_apply_7(v_k_517_, v_b_518_, v_c_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, lean_box(0));
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_526_, lean_object* v_b_527_, lean_object* v_c_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_526_, v_b_527_, v_c_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_535_, lean_object* v_k_536_, uint8_t v_cleanupAnnotations_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___f_543_; uint8_t v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_543_, 0, v_k_536_);
v___x_544_ = 1;
v___x_545_ = 0;
v___x_546_ = lean_box(0);
v___x_547_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_535_, v___x_544_, v___x_545_, v___x_544_, v___x_545_, v___x_546_, v___f_543_, v_cleanupAnnotations_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_547_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_547_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_564_, lean_object* v_k_565_, lean_object* v_cleanupAnnotations_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_572_; lean_object* v_res_573_; 
v_cleanupAnnotations_boxed_572_ = lean_unbox(v_cleanupAnnotations_566_);
v_res_573_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_564_, v_k_565_, v_cleanupAnnotations_boxed_572_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_574_, lean_object* v_e_575_, lean_object* v_k_576_, uint8_t v_cleanupAnnotations_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_575_, v_k_576_, v_cleanupAnnotations_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_584_, lean_object* v_e_585_, lean_object* v_k_586_, lean_object* v_cleanupAnnotations_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_593_; lean_object* v_res_594_; 
v_cleanupAnnotations_boxed_593_ = lean_unbox(v_cleanupAnnotations_587_);
v_res_594_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_584_, v_e_585_, v_k_586_, v_cleanupAnnotations_boxed_593_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
if (lean_obj_tag(v_a_595_) == 0)
{
lean_object* v___x_597_; 
v___x_597_ = l_List_reverse___redArg(v_a_596_);
return v___x_597_;
}
else
{
lean_object* v_head_598_; lean_object* v_tail_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_608_; 
v_head_598_ = lean_ctor_get(v_a_595_, 0);
v_tail_599_ = lean_ctor_get(v_a_595_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_a_595_);
if (v_isSharedCheck_608_ == 0)
{
v___x_601_ = v_a_595_;
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_tail_599_);
lean_inc(v_head_598_);
lean_dec(v_a_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = l_Lean_mkLevelParam(v_head_598_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v_a_596_);
lean_ctor_set(v___x_601_, 0, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_a_596_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v_a_595_ = v_tail_599_;
v_a_596_ = v___x_605_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_609_, lean_object* v_name_610_, lean_object* v_xs_611_, lean_object* v_body_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_name_618_; lean_object* v_levelParams_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_689_; 
v_name_618_ = lean_ctor_get(v_toConstantVal_609_, 0);
v_levelParams_619_ = lean_ctor_get(v_toConstantVal_609_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_toConstantVal_609_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v_toConstantVal_609_, 2);
lean_dec(v_unused_690_);
v___x_621_ = v_toConstantVal_609_;
v_isShared_622_ = v_isSharedCheck_689_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_levelParams_619_);
lean_inc(v_name_618_);
lean_dec(v_toConstantVal_609_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_689_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_lhs_626_; lean_object* v___x_627_; 
v___x_623_ = lean_box(0);
lean_inc(v_levelParams_619_);
v___x_624_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_619_, v___x_623_);
v___x_625_ = l_Lean_mkConst(v_name_618_, v___x_624_);
v_lhs_626_ = l_Lean_mkAppN(v___x_625_, v_xs_611_);
lean_inc_ref(v_lhs_626_);
v___x_627_ = l_Lean_Meta_mkEq(v_lhs_626_, v_body_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; uint8_t v___x_629_; uint8_t v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref(v___x_627_);
v___x_629_ = 0;
v___x_630_ = 1;
v___x_631_ = 1;
v___x_632_ = l_Lean_Meta_mkForallFVars(v_xs_611_, v_a_628_, v___x_629_, v___x_630_, v___x_630_, v___x_631_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_Lean_Meta_letToHave(v_a_633_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref(v___x_634_);
v___x_636_ = l_Lean_Meta_mkEqRefl(v_lhs_626_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref(v___x_636_);
v___x_638_ = l_Lean_Meta_mkLambdaFVars(v_xs_611_, v_a_637_, v___x_629_, v___x_630_, v___x_629_, v___x_630_, v___x_631_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
lean_inc(v_name_610_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 2, v_a_635_);
lean_ctor_set(v___x_621_, 0, v_name_610_);
v___x_641_ = v___x_621_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_name_610_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_levelParams_619_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_a_635_);
v___x_641_ = v_reuseFailAlloc_648_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_a_645_; lean_object* v___x_646_; 
lean_inc(v_name_610_);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v_name_610_);
lean_ctor_set(v___x_642_, 1, v___x_623_);
v___x_643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v_a_639_);
lean_ctor_set(v___x_643_, 2, v___x_642_);
v___x_644_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_643_, v___y_616_);
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref(v___x_644_);
v___x_646_ = l_Lean_addDecl(v_a_645_, v___x_629_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v___x_647_; 
lean_dec_ref(v___x_646_);
v___x_647_ = l_Lean_inferDefEqAttr(v_name_610_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_647_;
}
else
{
lean_dec(v_name_610_);
return v___x_646_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_635_);
lean_del_object(v___x_621_);
lean_dec(v_levelParams_619_);
lean_dec(v_name_610_);
v_a_649_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_638_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_638_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_a_635_);
lean_del_object(v___x_621_);
lean_dec(v_levelParams_619_);
lean_dec(v_name_610_);
v_a_657_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_636_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_636_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_lhs_626_);
lean_del_object(v___x_621_);
lean_dec(v_levelParams_619_);
lean_dec(v_name_610_);
v_a_665_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_634_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_634_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_lhs_626_);
lean_del_object(v___x_621_);
lean_dec(v_levelParams_619_);
lean_dec(v_name_610_);
v_a_673_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_632_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_632_);
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
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_lhs_626_);
lean_del_object(v___x_621_);
lean_dec(v_levelParams_619_);
lean_dec(v_name_610_);
v_a_681_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_627_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_627_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_691_, lean_object* v_name_692_, lean_object* v_xs_693_, lean_object* v_body_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_691_, v_name_692_, v_xs_693_, v_body_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v_xs_693_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_701_, lean_object* v_info_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_toConstantVal_708_; lean_object* v_value_709_; lean_object* v___f_710_; uint8_t v___x_711_; lean_object* v___x_712_; 
v_toConstantVal_708_ = lean_ctor_get(v_info_702_, 0);
lean_inc_ref(v_toConstantVal_708_);
v_value_709_ = lean_ctor_get(v_info_702_, 1);
lean_inc_ref(v_value_709_);
lean_dec_ref(v_info_702_);
v___f_710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_710_, 0, v_toConstantVal_708_);
lean_closure_set(v___f_710_, 1, v_name_701_);
v___x_711_ = 1;
v___x_712_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_709_, v___f_710_, v___x_711_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_713_, lean_object* v_info_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_713_, v_info_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_721_, lean_object* v_name_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_731_; lean_object* v_env_732_; uint8_t v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_st_ref_get(v_a_726_);
v_env_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_env_732_);
lean_dec(v___x_731_);
v___x_733_ = 0;
lean_inc(v_declName_721_);
v___x_734_ = l_Lean_Environment_find_x3f(v_env_732_, v_declName_721_, v___x_733_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_val_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_761_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_761_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_761_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_val_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_761_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
if (lean_obj_tag(v_val_735_) == 1)
{
lean_object* v_val_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_val_739_ = lean_ctor_get(v_val_735_, 0);
lean_inc_ref(v_val_739_);
lean_dec_ref(v_val_735_);
lean_inc_n(v_name_722_, 2);
v___x_740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_740_, 0, v_name_722_);
lean_closure_set(v___x_740_, 1, v_val_739_);
v___x_741_ = l_Lean_Meta_realizeConst(v_declName_721_, v_name_722_, v___x_740_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_751_; 
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v___x_741_, 0);
lean_dec(v_unused_752_);
v___x_743_ = v___x_741_;
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
else
{
lean_dec(v___x_741_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_name_722_);
v___x_746_ = v___x_737_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_name_722_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_746_);
v___x_748_ = v___x_743_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_del_object(v___x_737_);
lean_dec(v_name_722_);
v_a_753_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_741_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_741_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_del_object(v___x_737_);
lean_dec(v_val_735_);
lean_dec(v_name_722_);
lean_dec(v_declName_721_);
goto v___jp_728_;
}
}
}
else
{
lean_dec(v___x_734_);
lean_dec(v_name_722_);
lean_dec(v_declName_721_);
goto v___jp_728_;
}
v___jp_728_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_box(0);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_762_, lean_object* v_name_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_mkSimpleEqThm(v_declName_762_, v_name_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_770_, lean_object* v_vals_771_, lean_object* v_i_772_, lean_object* v_k_773_){
_start:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_get_size(v_keys_770_);
v___x_775_ = lean_nat_dec_lt(v_i_772_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec(v_i_772_);
v___x_776_ = lean_box(0);
return v___x_776_;
}
else
{
lean_object* v_k_x27_777_; uint8_t v___x_778_; 
v_k_x27_777_ = lean_array_fget_borrowed(v_keys_770_, v_i_772_);
v___x_778_ = lean_name_eq(v_k_773_, v_k_x27_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_i_772_, v___x_779_);
lean_dec(v_i_772_);
v_i_772_ = v___x_780_;
goto _start;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_array_fget_borrowed(v_vals_771_, v_i_772_);
lean_dec(v_i_772_);
lean_inc(v___x_782_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_i_786_, lean_object* v_k_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_784_, v_vals_785_, v_i_786_, v_k_787_);
lean_dec(v_k_787_);
lean_dec_ref(v_vals_785_);
lean_dec_ref(v_keys_784_);
return v_res_788_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; 
v___x_789_ = ((size_t)5ULL);
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_shift_left(v___x_790_, v___x_789_);
return v___x_791_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; 
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_794_ = lean_usize_sub(v___x_793_, v___x_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_795_, size_t v_x_796_, lean_object* v_x_797_){
_start:
{
if (lean_obj_tag(v_x_795_) == 0)
{
lean_object* v_es_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_819_; 
v_es_798_ = lean_ctor_get(v_x_795_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_819_ == 0)
{
v___x_800_ = v_x_795_;
v_isShared_801_ = v_isSharedCheck_819_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_es_798_);
lean_dec(v_x_795_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_819_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v_j_806_; lean_object* v___x_807_; 
v___x_802_ = lean_box(2);
v___x_803_ = ((size_t)5ULL);
v___x_804_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_805_ = lean_usize_land(v_x_796_, v___x_804_);
v_j_806_ = lean_usize_to_nat(v___x_805_);
v___x_807_ = lean_array_get(v___x_802_, v_es_798_, v_j_806_);
lean_dec(v_j_806_);
lean_dec_ref(v_es_798_);
switch(lean_obj_tag(v___x_807_))
{
case 0:
{
lean_object* v_key_808_; lean_object* v_val_809_; uint8_t v___x_810_; 
v_key_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_key_808_);
v_val_809_ = lean_ctor_get(v___x_807_, 1);
lean_inc(v_val_809_);
lean_dec_ref(v___x_807_);
v___x_810_ = lean_name_eq(v_x_797_, v_key_808_);
lean_dec(v_key_808_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_dec(v_val_809_);
lean_del_object(v___x_800_);
v___x_811_ = lean_box(0);
return v___x_811_;
}
else
{
lean_object* v___x_813_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 1);
lean_ctor_set(v___x_800_, 0, v_val_809_);
v___x_813_ = v___x_800_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_val_809_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
case 1:
{
lean_object* v_node_815_; size_t v___x_816_; 
lean_del_object(v___x_800_);
v_node_815_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_node_815_);
lean_dec_ref(v___x_807_);
v___x_816_ = lean_usize_shift_right(v_x_796_, v___x_803_);
v_x_795_ = v_node_815_;
v_x_796_ = v___x_816_;
goto _start;
}
default: 
{
lean_object* v___x_818_; 
lean_del_object(v___x_800_);
v___x_818_ = lean_box(0);
return v___x_818_;
}
}
}
}
else
{
lean_object* v_ks_820_; lean_object* v_vs_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_ks_820_ = lean_ctor_get(v_x_795_, 0);
lean_inc_ref(v_ks_820_);
v_vs_821_ = lean_ctor_get(v_x_795_, 1);
lean_inc_ref(v_vs_821_);
lean_dec_ref(v_x_795_);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_820_, v_vs_821_, v___x_822_, v_x_797_);
lean_dec_ref(v_vs_821_);
lean_dec_ref(v_ks_820_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
size_t v_x_355__boxed_827_; lean_object* v_res_828_; 
v_x_355__boxed_827_ = lean_unbox_usize(v_x_825_);
lean_dec(v_x_825_);
v_res_828_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_824_, v_x_355__boxed_827_, v_x_826_);
lean_dec(v_x_826_);
return v_res_828_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_829_; uint64_t v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(1723u);
v___x_830_ = lean_uint64_of_nat(v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
uint64_t v___y_834_; 
if (lean_obj_tag(v_x_832_) == 0)
{
uint64_t v___x_837_; 
v___x_837_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_834_ = v___x_837_;
goto v___jp_833_;
}
else
{
uint64_t v_hash_838_; 
v_hash_838_ = lean_ctor_get_uint64(v_x_832_, sizeof(void*)*2);
v___y_834_ = v_hash_838_;
goto v___jp_833_;
}
v___jp_833_:
{
size_t v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_uint64_to_usize(v___y_834_);
v___x_836_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_831_, v___x_835_, v_x_832_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_839_, v_x_840_);
lean_dec(v_x_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; lean_object* v_env_846_; lean_object* v___x_847_; lean_object* v_asyncMode_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_845_ = lean_st_ref_get(v_a_843_);
v_env_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc_ref(v_env_846_);
lean_dec(v___x_845_);
v___x_847_ = l_Lean_Meta_eqnsExt;
v_asyncMode_848_ = lean_ctor_get(v___x_847_, 2);
v___x_849_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_850_ = lean_box(0);
v___x_851_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_849_, v___x_847_, v_env_846_, v_asyncMode_848_, v___x_850_);
v___x_852_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_851_, v_thmName_842_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec(v_thmName_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_858_, v_a_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_thmName_863_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_872_, v_x_873_, v_x_874_);
lean_dec(v_x_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, size_t v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_877_, v_x_878_, v_x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
size_t v_x_472__boxed_885_; lean_object* v_res_886_; 
v_x_472__boxed_885_ = lean_unbox_usize(v_x_883_);
lean_dec(v_x_883_);
v_res_886_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_881_, v_x_882_, v_x_472__boxed_885_, v_x_884_);
lean_dec(v_x_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_887_, lean_object* v_keys_888_, lean_object* v_vals_889_, lean_object* v_heq_890_, lean_object* v_i_891_, lean_object* v_k_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_888_, v_vals_889_, v_i_891_, v_k_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_heq_897_, lean_object* v_i_898_, lean_object* v_k_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_894_, v_keys_895_, v_vals_896_, v_heq_897_, v_i_898_, v_k_899_);
lean_dec(v_k_899_);
lean_dec_ref(v_vals_896_);
lean_dec_ref(v_keys_895_);
return v_res_900_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_901_, lean_object* v_i_902_, lean_object* v_k_903_){
_start:
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_array_get_size(v_keys_901_);
v___x_905_ = lean_nat_dec_lt(v_i_902_, v___x_904_);
if (v___x_905_ == 0)
{
lean_dec(v_i_902_);
return v___x_905_;
}
else
{
lean_object* v_k_x27_906_; uint8_t v___x_907_; 
v_k_x27_906_ = lean_array_fget_borrowed(v_keys_901_, v_i_902_);
v___x_907_ = lean_name_eq(v_k_903_, v_k_x27_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_add(v_i_902_, v___x_908_);
lean_dec(v_i_902_);
v_i_902_ = v___x_909_;
goto _start;
}
else
{
lean_dec(v_i_902_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_911_, lean_object* v_i_912_, lean_object* v_k_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_911_, v_i_912_, v_k_913_);
lean_dec(v_k_913_);
lean_dec_ref(v_keys_911_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_916_, size_t v_x_917_, lean_object* v_x_918_){
_start:
{
if (lean_obj_tag(v_x_916_) == 0)
{
lean_object* v_es_919_; lean_object* v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; lean_object* v_j_924_; lean_object* v___x_925_; 
v_es_919_ = lean_ctor_get(v_x_916_, 0);
v___x_920_ = lean_box(2);
v___x_921_ = ((size_t)5ULL);
v___x_922_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_923_ = lean_usize_land(v_x_917_, v___x_922_);
v_j_924_ = lean_usize_to_nat(v___x_923_);
v___x_925_ = lean_array_get_borrowed(v___x_920_, v_es_919_, v_j_924_);
lean_dec(v_j_924_);
switch(lean_obj_tag(v___x_925_))
{
case 0:
{
lean_object* v_key_926_; uint8_t v___x_927_; 
v_key_926_ = lean_ctor_get(v___x_925_, 0);
v___x_927_ = lean_name_eq(v_x_918_, v_key_926_);
return v___x_927_;
}
case 1:
{
lean_object* v_node_928_; size_t v___x_929_; 
v_node_928_ = lean_ctor_get(v___x_925_, 0);
v___x_929_ = lean_usize_shift_right(v_x_917_, v___x_921_);
v_x_916_ = v_node_928_;
v_x_917_ = v___x_929_;
goto _start;
}
default: 
{
uint8_t v___x_931_; 
v___x_931_ = 0;
return v___x_931_;
}
}
}
else
{
lean_object* v_ks_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_ks_932_ = lean_ctor_get(v_x_916_, 0);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_932_, v___x_933_, v_x_918_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
size_t v_x_335__boxed_938_; uint8_t v_res_939_; lean_object* v_r_940_; 
v_x_335__boxed_938_ = lean_unbox_usize(v_x_936_);
lean_dec(v_x_936_);
v_res_939_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_935_, v_x_335__boxed_938_, v_x_937_);
lean_dec(v_x_937_);
lean_dec_ref(v_x_935_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
uint64_t v___y_944_; 
if (lean_obj_tag(v_x_942_) == 0)
{
uint64_t v___x_947_; 
v___x_947_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_944_ = v___x_947_;
goto v___jp_943_;
}
else
{
uint64_t v_hash_948_; 
v_hash_948_ = lean_ctor_get_uint64(v_x_942_, sizeof(void*)*2);
v___y_944_ = v_hash_948_;
goto v___jp_943_;
}
v___jp_943_:
{
size_t v___x_945_; uint8_t v___x_946_; 
v___x_945_ = lean_uint64_to_usize(v___y_944_);
v___x_946_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_941_, v___x_945_, v_x_942_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_949_, v_x_950_);
lean_dec(v_x_950_);
lean_dec_ref(v_x_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; lean_object* v_env_957_; lean_object* v___x_958_; lean_object* v_asyncMode_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_956_ = lean_st_ref_get(v_a_954_);
v_env_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc_ref(v_env_957_);
lean_dec(v___x_956_);
v___x_958_ = l_Lean_Meta_eqnsExt;
v_asyncMode_959_ = lean_ctor_get(v___x_958_, 2);
v___x_960_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_961_ = lean_box(0);
v___x_962_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_960_, v___x_958_, v_env_957_, v_asyncMode_959_, v___x_961_);
v___x_963_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_962_, v_thmName_953_);
lean_dec(v___x_962_);
v___x_964_ = lean_box(v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec(v_thmName_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_970_, v_a_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_isEqnThm(v_thmName_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_thmName_975_);
return v_res_979_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_981_, v_x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
uint8_t v_res_987_; lean_object* v_r_988_; 
v_res_987_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_984_, v_x_985_, v_x_986_);
lean_dec(v_x_986_);
lean_dec_ref(v_x_985_);
v_r_988_ = lean_box(v_res_987_);
return v_r_988_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, size_t v_x_991_, lean_object* v_x_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_990_, v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
size_t v_x_429__boxed_998_; uint8_t v_res_999_; lean_object* v_r_1000_; 
v_x_429__boxed_998_ = lean_unbox_usize(v_x_996_);
lean_dec(v_x_996_);
v_res_999_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_994_, v_x_995_, v_x_429__boxed_998_, v_x_997_);
lean_dec(v_x_997_);
lean_dec_ref(v_x_995_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1001_, lean_object* v_keys_1002_, lean_object* v_vals_1003_, lean_object* v_heq_1004_, lean_object* v_i_1005_, lean_object* v_k_1006_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1002_, v_i_1005_, v_k_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1008_, lean_object* v_keys_1009_, lean_object* v_vals_1010_, lean_object* v_heq_1011_, lean_object* v_i_1012_, lean_object* v_k_1013_){
_start:
{
uint8_t v_res_1014_; lean_object* v_r_1015_; 
v_res_1014_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1008_, v_keys_1009_, v_vals_1010_, v_heq_1011_, v_i_1012_, v_k_1013_);
lean_dec(v_k_1013_);
lean_dec_ref(v_vals_1010_);
lean_dec_ref(v_keys_1009_);
v_r_1015_ = lean_box(v_res_1014_);
return v_r_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v_ks_1020_; lean_object* v_vs_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1045_; 
v_ks_1020_ = lean_ctor_get(v_x_1016_, 0);
v_vs_1021_ = lean_ctor_get(v_x_1016_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1023_ = v_x_1016_;
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_vs_1021_);
lean_inc(v_ks_1020_);
lean_dec(v_x_1016_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = lean_array_get_size(v_ks_1020_);
v___x_1026_ = lean_nat_dec_lt(v_x_1017_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
lean_dec(v_x_1017_);
v___x_1027_ = lean_array_push(v_ks_1020_, v_x_1018_);
v___x_1028_ = lean_array_push(v_vs_1021_, v_x_1019_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1028_);
lean_ctor_set(v___x_1023_, 0, v___x_1027_);
v___x_1030_ = v___x_1023_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
lean_object* v_k_x27_1032_; uint8_t v___x_1033_; 
v_k_x27_1032_ = lean_array_fget_borrowed(v_ks_1020_, v_x_1017_);
v___x_1033_ = lean_name_eq(v_x_1018_, v_k_x27_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1035_; 
if (v_isShared_1024_ == 0)
{
v___x_1035_ = v___x_1023_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_ks_1020_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_vs_1021_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_nat_add(v_x_1017_, v___x_1036_);
lean_dec(v_x_1017_);
v_x_1016_ = v___x_1035_;
v_x_1017_ = v___x_1037_;
goto _start;
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1040_ = lean_array_fset(v_ks_1020_, v_x_1017_, v_x_1018_);
v___x_1041_ = lean_array_fset(v_vs_1021_, v_x_1017_, v_x_1019_);
lean_dec(v_x_1017_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1041_);
lean_ctor_set(v___x_1023_, 0, v___x_1040_);
v___x_1043_ = v___x_1023_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1046_, lean_object* v_k_1047_, lean_object* v_v_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1046_, v___x_1049_, v_k_1047_, v_v_1048_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1052_, size_t v_x_1053_, size_t v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
lean_object* v_es_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; lean_object* v_j_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_es_1057_ = lean_ctor_get(v_x_1052_, 0);
v___x_1058_ = ((size_t)5ULL);
v___x_1059_ = ((size_t)1ULL);
v___x_1060_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1061_ = lean_usize_land(v_x_1053_, v___x_1060_);
v_j_1062_ = lean_usize_to_nat(v___x_1061_);
v___x_1063_ = lean_array_get_size(v_es_1057_);
v___x_1064_ = lean_nat_dec_lt(v_j_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_dec(v_j_1062_);
lean_dec(v_x_1056_);
lean_dec(v_x_1055_);
return v_x_1052_;
}
else
{
lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1101_; 
lean_inc_ref(v_es_1057_);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v_x_1052_, 0);
lean_dec(v_unused_1102_);
v___x_1066_ = v_x_1052_;
v_isShared_1067_ = v_isSharedCheck_1101_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v_x_1052_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1101_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_v_1068_; lean_object* v___x_1069_; lean_object* v_xs_x27_1070_; lean_object* v___y_1072_; 
v_v_1068_ = lean_array_fget(v_es_1057_, v_j_1062_);
v___x_1069_ = lean_box(0);
v_xs_x27_1070_ = lean_array_fset(v_es_1057_, v_j_1062_, v___x_1069_);
switch(lean_obj_tag(v_v_1068_))
{
case 0:
{
lean_object* v_key_1077_; lean_object* v_val_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1088_; 
v_key_1077_ = lean_ctor_get(v_v_1068_, 0);
v_val_1078_ = lean_ctor_get(v_v_1068_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_v_1068_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1080_ = v_v_1068_;
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_val_1078_);
lean_inc(v_key_1077_);
lean_dec(v_v_1068_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_name_eq(v_x_1055_, v_key_1077_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_del_object(v___x_1080_);
v___x_1083_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1077_, v_val_1078_, v_x_1055_, v_x_1056_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
v___y_1072_ = v___x_1084_;
goto v___jp_1071_;
}
else
{
lean_object* v___x_1086_; 
lean_dec(v_val_1078_);
lean_dec(v_key_1077_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v_x_1056_);
lean_ctor_set(v___x_1080_, 0, v_x_1055_);
v___x_1086_ = v___x_1080_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_x_1055_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_x_1056_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
v___y_1072_ = v___x_1086_;
goto v___jp_1071_;
}
}
}
}
case 1:
{
lean_object* v_node_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1099_; 
v_node_1089_ = lean_ctor_get(v_v_1068_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_v_1068_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1091_ = v_v_1068_;
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_node_1089_);
lean_dec(v_v_1068_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1093_ = lean_usize_shift_right(v_x_1053_, v___x_1058_);
v___x_1094_ = lean_usize_add(v_x_1054_, v___x_1059_);
v___x_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1089_, v___x_1093_, v___x_1094_, v_x_1055_, v_x_1056_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1095_);
v___x_1097_ = v___x_1091_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
v___y_1072_ = v___x_1097_;
goto v___jp_1071_;
}
}
}
default: 
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_x_1055_);
lean_ctor_set(v___x_1100_, 1, v_x_1056_);
v___y_1072_ = v___x_1100_;
goto v___jp_1071_;
}
}
v___jp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = lean_array_fset(v_xs_x27_1070_, v_j_1062_, v___y_1072_);
lean_dec(v_j_1062_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1073_);
v___x_1075_ = v___x_1066_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
else
{
lean_object* v_ks_1103_; lean_object* v_vs_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1124_; 
v_ks_1103_ = lean_ctor_get(v_x_1052_, 0);
v_vs_1104_ = lean_ctor_get(v_x_1052_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1106_ = v_x_1052_;
v_isShared_1107_ = v_isSharedCheck_1124_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_vs_1104_);
lean_inc(v_ks_1103_);
lean_dec(v_x_1052_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1124_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_ks_1103_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_vs_1104_);
v___x_1109_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v_newNode_1110_; uint8_t v___y_1112_; size_t v___x_1118_; uint8_t v___x_1119_; 
v_newNode_1110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1109_, v_x_1055_, v_x_1056_);
v___x_1118_ = ((size_t)7ULL);
v___x_1119_ = lean_usize_dec_le(v___x_1118_, v_x_1054_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1110_);
v___x_1121_ = lean_unsigned_to_nat(4u);
v___x_1122_ = lean_nat_dec_lt(v___x_1120_, v___x_1121_);
lean_dec(v___x_1120_);
v___y_1112_ = v___x_1122_;
goto v___jp_1111_;
}
else
{
v___y_1112_ = v___x_1119_;
goto v___jp_1111_;
}
v___jp_1111_:
{
if (v___y_1112_ == 0)
{
lean_object* v_ks_1113_; lean_object* v_vs_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_ks_1113_ = lean_ctor_get(v_newNode_1110_, 0);
lean_inc_ref(v_ks_1113_);
v_vs_1114_ = lean_ctor_get(v_newNode_1110_, 1);
lean_inc_ref(v_vs_1114_);
lean_dec_ref(v_newNode_1110_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1054_, v_ks_1113_, v_vs_1114_, v___x_1115_, v___x_1116_);
lean_dec_ref(v_vs_1114_);
lean_dec_ref(v_ks_1113_);
return v___x_1117_;
}
else
{
return v_newNode_1110_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1125_, lean_object* v_keys_1126_, lean_object* v_vals_1127_, lean_object* v_i_1128_, lean_object* v_entries_1129_){
_start:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_array_get_size(v_keys_1126_);
v___x_1131_ = lean_nat_dec_lt(v_i_1128_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_dec(v_i_1128_);
return v_entries_1129_;
}
else
{
lean_object* v_k_1132_; lean_object* v_v_1133_; uint64_t v___y_1135_; 
v_k_1132_ = lean_array_fget_borrowed(v_keys_1126_, v_i_1128_);
v_v_1133_ = lean_array_fget_borrowed(v_vals_1127_, v_i_1128_);
if (lean_obj_tag(v_k_1132_) == 0)
{
uint64_t v___x_1146_; 
v___x_1146_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1135_ = v___x_1146_;
goto v___jp_1134_;
}
else
{
uint64_t v_hash_1147_; 
v_hash_1147_ = lean_ctor_get_uint64(v_k_1132_, sizeof(void*)*2);
v___y_1135_ = v_hash_1147_;
goto v___jp_1134_;
}
v___jp_1134_:
{
size_t v_h_1136_; size_t v___x_1137_; lean_object* v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; size_t v_h_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_h_1136_ = lean_uint64_to_usize(v___y_1135_);
v___x_1137_ = ((size_t)5ULL);
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = ((size_t)1ULL);
v___x_1140_ = lean_usize_sub(v_depth_1125_, v___x_1139_);
v___x_1141_ = lean_usize_mul(v___x_1137_, v___x_1140_);
v_h_1142_ = lean_usize_shift_right(v_h_1136_, v___x_1141_);
v___x_1143_ = lean_nat_add(v_i_1128_, v___x_1138_);
lean_dec(v_i_1128_);
lean_inc(v_v_1133_);
lean_inc(v_k_1132_);
v___x_1144_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1129_, v_h_1142_, v_depth_1125_, v_k_1132_, v_v_1133_);
v_i_1128_ = v___x_1143_;
v_entries_1129_ = v___x_1144_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1148_, lean_object* v_keys_1149_, lean_object* v_vals_1150_, lean_object* v_i_1151_, lean_object* v_entries_1152_){
_start:
{
size_t v_depth_boxed_1153_; lean_object* v_res_1154_; 
v_depth_boxed_1153_ = lean_unbox_usize(v_depth_1148_);
lean_dec(v_depth_1148_);
v_res_1154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1153_, v_keys_1149_, v_vals_1150_, v_i_1151_, v_entries_1152_);
lean_dec_ref(v_vals_1150_);
lean_dec_ref(v_keys_1149_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_){
_start:
{
size_t v_x_634__boxed_1160_; size_t v_x_635__boxed_1161_; lean_object* v_res_1162_; 
v_x_634__boxed_1160_ = lean_unbox_usize(v_x_1156_);
lean_dec(v_x_1156_);
v_x_635__boxed_1161_ = lean_unbox_usize(v_x_1157_);
lean_dec(v_x_1157_);
v_res_1162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1155_, v_x_634__boxed_1160_, v_x_635__boxed_1161_, v_x_1158_, v_x_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
uint64_t v___y_1167_; 
if (lean_obj_tag(v_x_1164_) == 0)
{
uint64_t v___x_1171_; 
v___x_1171_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1167_ = v___x_1171_;
goto v___jp_1166_;
}
else
{
uint64_t v_hash_1172_; 
v_hash_1172_ = lean_ctor_get_uint64(v_x_1164_, sizeof(void*)*2);
v___y_1167_ = v_hash_1172_;
goto v___jp_1166_;
}
v___jp_1166_:
{
size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_uint64_to_usize(v___y_1167_);
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1163_, v___x_1168_, v___x_1169_, v_x_1164_, v_x_1165_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1173_, lean_object* v_as_1174_, size_t v_i_1175_, size_t v_stop_1176_, lean_object* v_b_1177_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_eq(v_i_1175_, v_stop_1176_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; 
v___x_1179_ = lean_array_uget_borrowed(v_as_1174_, v_i_1175_);
lean_inc(v_declName_1173_);
lean_inc(v___x_1179_);
v___x_1180_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1177_, v___x_1179_, v_declName_1173_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1175_, v___x_1181_);
v_i_1175_ = v___x_1182_;
v_b_1177_ = v___x_1180_;
goto _start;
}
else
{
lean_dec(v_declName_1173_);
return v_b_1177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1184_, lean_object* v_as_1185_, lean_object* v_i_1186_, lean_object* v_stop_1187_, lean_object* v_b_1188_){
_start:
{
size_t v_i_boxed_1189_; size_t v_stop_boxed_1190_; lean_object* v_res_1191_; 
v_i_boxed_1189_ = lean_unbox_usize(v_i_1186_);
lean_dec(v_i_1186_);
v_stop_boxed_1190_ = lean_unbox_usize(v_stop_1187_);
lean_dec(v_stop_1187_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1184_, v_as_1185_, v_i_boxed_1189_, v_stop_boxed_1190_, v_b_1188_);
lean_dec_ref(v_as_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1192_, lean_object* v_declName_1193_, lean_object* v_s_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = lean_array_get_size(v_eqThms_1192_);
v___x_1197_ = lean_nat_dec_lt(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_dec(v_declName_1193_);
return v_s_1194_;
}
else
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_nat_dec_le(v___x_1196_, v___x_1196_);
if (v___x_1198_ == 0)
{
if (v___x_1197_ == 0)
{
lean_dec(v_declName_1193_);
return v_s_1194_;
}
else
{
size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((size_t)0ULL);
v___x_1200_ = lean_usize_of_nat(v___x_1196_);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1193_, v_eqThms_1192_, v___x_1199_, v___x_1200_, v_s_1194_);
return v___x_1201_;
}
}
else
{
size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = ((size_t)0ULL);
v___x_1203_ = lean_usize_of_nat(v___x_1196_);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1193_, v_eqThms_1192_, v___x_1202_, v___x_1203_, v_s_1194_);
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1205_, lean_object* v_declName_1206_, lean_object* v_s_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1205_, v_declName_1206_, v_s_1207_);
lean_dec_ref(v_eqThms_1205_);
return v_res_1208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0(void){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1214_, lean_object* v_eqThms_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v_env_1219_; lean_object* v_nextMacroScope_1220_; lean_object* v_ngen_1221_; lean_object* v_auxDeclNGen_1222_; lean_object* v_traceState_1223_; lean_object* v_messages_1224_; lean_object* v_infoState_1225_; lean_object* v_snapshotTasks_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1242_; 
v___x_1218_ = lean_st_ref_take(v_a_1216_);
v_env_1219_ = lean_ctor_get(v___x_1218_, 0);
v_nextMacroScope_1220_ = lean_ctor_get(v___x_1218_, 1);
v_ngen_1221_ = lean_ctor_get(v___x_1218_, 2);
v_auxDeclNGen_1222_ = lean_ctor_get(v___x_1218_, 3);
v_traceState_1223_ = lean_ctor_get(v___x_1218_, 4);
v_messages_1224_ = lean_ctor_get(v___x_1218_, 6);
v_infoState_1225_ = lean_ctor_get(v___x_1218_, 7);
v_snapshotTasks_1226_ = lean_ctor_get(v___x_1218_, 8);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1218_, 5);
lean_dec(v_unused_1243_);
v___x_1228_ = v___x_1218_;
v_isShared_1229_ = v_isSharedCheck_1242_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_snapshotTasks_1226_);
lean_inc(v_infoState_1225_);
lean_inc(v_messages_1224_);
lean_inc(v_traceState_1223_);
lean_inc(v_auxDeclNGen_1222_);
lean_inc(v_ngen_1221_);
lean_inc(v_nextMacroScope_1220_);
lean_inc(v_env_1219_);
lean_dec(v___x_1218_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1242_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v_asyncMode_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1230_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1231_ = lean_ctor_get(v___x_1230_, 2);
v___f_1232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1232_, 0, v_eqThms_1215_);
lean_closure_set(v___f_1232_, 1, v_declName_1214_);
v___x_1233_ = lean_box(0);
v___x_1234_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1230_, v_env_1219_, v___f_1232_, v_asyncMode_1231_, v___x_1233_);
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 5, v___x_1235_);
lean_ctor_set(v___x_1228_, 0, v___x_1234_);
v___x_1237_ = v___x_1228_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_nextMacroScope_1220_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_ngen_1221_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_auxDeclNGen_1222_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_traceState_1223_);
lean_ctor_set(v_reuseFailAlloc_1241_, 5, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1241_, 6, v_messages_1224_);
lean_ctor_set(v_reuseFailAlloc_1241_, 7, v_infoState_1225_);
lean_ctor_set(v_reuseFailAlloc_1241_, 8, v_snapshotTasks_1226_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_st_ref_set(v_a_1216_, v___x_1237_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1244_, lean_object* v_eqThms_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1244_, v_eqThms_1245_, v_a_1246_);
lean_dec(v_a_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1249_, lean_object* v_eqThms_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1249_, v_eqThms_1250_, v_a_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1255_, lean_object* v_eqThms_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1255_, v_eqThms_1256_, v_a_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1262_, v_x_1263_, v_x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1266_, lean_object* v_x_1267_, size_t v_x_1268_, size_t v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1267_, v_x_1268_, v_x_1269_, v_x_1270_, v_x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
size_t v_x_912__boxed_1279_; size_t v_x_913__boxed_1280_; lean_object* v_res_1281_; 
v_x_912__boxed_1279_ = lean_unbox_usize(v_x_1275_);
lean_dec(v_x_1275_);
v_x_913__boxed_1280_ = lean_unbox_usize(v_x_1276_);
lean_dec(v_x_1276_);
v_res_1281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1273_, v_x_1274_, v_x_912__boxed_1279_, v_x_913__boxed_1280_, v_x_1277_, v_x_1278_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1282_, lean_object* v_n_1283_, lean_object* v_k_1284_, lean_object* v_v_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1283_, v_k_1284_, v_v_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1287_, size_t v_depth_1288_, lean_object* v_keys_1289_, lean_object* v_vals_1290_, lean_object* v_heq_1291_, lean_object* v_i_1292_, lean_object* v_entries_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1288_, v_keys_1289_, v_vals_1290_, v_i_1292_, v_entries_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1295_, lean_object* v_depth_1296_, lean_object* v_keys_1297_, lean_object* v_vals_1298_, lean_object* v_heq_1299_, lean_object* v_i_1300_, lean_object* v_entries_1301_){
_start:
{
size_t v_depth_boxed_1302_; lean_object* v_res_1303_; 
v_depth_boxed_1302_ = lean_unbox_usize(v_depth_1296_);
lean_dec(v_depth_1296_);
v_res_1303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1295_, v_depth_boxed_1302_, v_keys_1297_, v_vals_1298_, v_heq_1299_, v_i_1300_, v_entries_1301_);
lean_dec_ref(v_vals_1298_);
lean_dec_ref(v_keys_1297_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1305_, v_x_1306_, v_x_1307_, v_x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1310_, lean_object* v_env_1311_, lean_object* v_idx_1312_, lean_object* v_eqs_1313_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_nextEq_1320_; uint8_t v___x_1321_; 
v___x_1315_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_add(v_idx_1312_, v___x_1316_);
lean_dec(v_idx_1312_);
lean_inc(v___x_1317_);
v___x_1318_ = l_Nat_reprFast(v___x_1317_);
v___x_1319_ = lean_string_append(v___x_1315_, v___x_1318_);
lean_dec_ref(v___x_1318_);
lean_inc(v_declName_1310_);
lean_inc_ref(v_env_1311_);
v_nextEq_1320_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1311_, v_declName_1310_, v___x_1319_);
v___x_1321_ = l_Lean_Environment_containsOnBranch(v_env_1311_, v_nextEq_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_dec(v_nextEq_1320_);
lean_dec(v___x_1317_);
lean_dec_ref(v_env_1311_);
lean_dec(v_declName_1310_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_eqs_1313_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_array_push(v_eqs_1313_, v_nextEq_1320_);
v_idx_1312_ = v___x_1317_;
v_eqs_1313_ = v___x_1323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1325_, lean_object* v_env_1326_, lean_object* v_idx_1327_, lean_object* v_eqs_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1325_, v_env_1326_, v_idx_1327_, v_eqs_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1331_, lean_object* v_env_1332_, lean_object* v_idx_1333_, lean_object* v_eqs_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1331_, v_env_1332_, v_idx_1333_, v_eqs_1334_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1341_, lean_object* v_env_1342_, lean_object* v_idx_1343_, lean_object* v_eqs_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1341_, v_env_1342_, v_idx_1343_, v_eqs_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v_env_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1354_ = lean_st_ref_get(v_a_1352_);
v_env_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc_ref_n(v_env_1355_, 3);
lean_dec(v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1351_);
v___x_1357_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1355_, v_declName_1351_, v___x_1356_);
v___x_1358_ = 1;
lean_inc(v___x_1357_);
v___x_1359_ = l_Lean_Environment_contains(v_env_1355_, v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec(v___x_1357_);
lean_dec_ref(v_env_1355_);
lean_dec(v_declName_1351_);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_mk_empty_array_with_capacity(v___x_1362_);
v___x_1364_ = lean_array_push(v___x_1363_, v___x_1357_);
lean_inc(v_declName_1351_);
v___x_1365_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1351_, v_env_1355_, v___x_1362_, v___x_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc_n(v_a_1366_, 2);
lean_dec_ref(v___x_1365_);
v___x_1367_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1351_, v_a_1366_, v_a_1352_);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1367_, 0);
lean_dec(v_unused_1376_);
v___x_1369_ = v___x_1367_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v___x_1367_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_a_1366_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_declName_1351_);
v_a_1377_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1365_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1365_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1385_, v_a_1386_);
lean_dec(v_a_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1389_, v_a_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1403_, lean_object* v_localInsts_1404_, lean_object* v_x_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1403_, v_localInsts_1404_, v_x_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_a_1420_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1411_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1411_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1428_, lean_object* v_localInsts_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1428_, v_localInsts_1429_, v_x_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1437_, lean_object* v_lctx_1438_, lean_object* v_localInsts_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1438_, v_localInsts_1439_, v_x_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_lctx_1448_, lean_object* v_localInsts_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1447_, v_lctx_1448_, v_localInsts_1449_, v_x_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1460_, lean_object* v_as_x27_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
if (lean_obj_tag(v_as_x27_1461_) == 0)
{
lean_object* v___x_1468_; 
lean_dec(v_declName_1460_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_b_1462_);
return v___x_1468_;
}
else
{
lean_object* v_head_1469_; lean_object* v_tail_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_b_1462_);
v_head_1469_ = lean_ctor_get(v_as_x27_1461_, 0);
v_tail_1470_ = lean_ctor_get(v_as_x27_1461_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_as_x27_1461_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1472_ = v_as_x27_1461_;
v_isShared_1473_ = v_isSharedCheck_1501_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_tail_1470_);
lean_inc(v_head_1469_);
lean_dec(v_as_x27_1461_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1501_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; 
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v_declName_1460_);
v___x_1474_ = lean_apply_6(v_head_1469_, v_declName_1460_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, lean_box(0));
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref(v___x_1474_);
v___x_1476_ = lean_box(0);
if (lean_obj_tag(v_a_1475_) == 1)
{
lean_object* v_val_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_tail_1470_);
v_val_1477_ = lean_ctor_get(v_a_1475_, 0);
lean_inc(v_val_1477_);
v___x_1478_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1460_, v_val_1477_, v___y_1466_);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1490_);
v___x_1480_ = v___x_1478_;
v_isShared_1481_ = v_isSharedCheck_1489_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v___x_1478_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1489_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_a_1475_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 0);
lean_ctor_set(v___x_1472_, 1, v___x_1476_);
lean_ctor_set(v___x_1472_, 0, v___x_1482_);
v___x_1484_ = v___x_1472_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1476_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1484_);
v___x_1486_ = v___x_1480_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
v___x_1491_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1461_ = v_tail_1470_;
v_b_1462_ = v___x_1491_;
goto _start;
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_del_object(v___x_1472_);
lean_dec(v_tail_1470_);
lean_dec(v_declName_1460_);
v_a_1493_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1474_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1474_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1502_, lean_object* v_as_x27_1503_, lean_object* v_b_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1502_, v_as_x27_1503_, v_b_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
lean_inc(v_declName_1511_);
v___x_1517_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1555_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1555_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1555_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_unbox(v_a_1518_);
lean_dec(v_a_1518_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
lean_dec(v_declName_1511_);
v___x_1523_ = lean_box(0);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
else
{
lean_object* v___x_1527_; 
lean_del_object(v___x_1520_);
lean_inc(v_declName_1511_);
v___x_1527_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1511_, v___y_1515_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
if (lean_obj_tag(v_a_1528_) == 1)
{
lean_dec_ref(v_a_1528_);
lean_dec(v_declName_1511_);
return v___x_1527_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_a_1528_);
lean_dec_ref(v___x_1527_);
v___x_1529_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1530_ = lean_st_ref_get(v___x_1529_);
v___x_1531_ = lean_box(0);
v___x_1532_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1533_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1511_, v___x_1530_, v___x_1532_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1546_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1546_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1546_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_fst_1538_; 
v_fst_1538_ = lean_ctor_get(v_a_1534_, 0);
lean_inc(v_fst_1538_);
lean_dec(v_a_1534_);
if (lean_obj_tag(v_fst_1538_) == 0)
{
lean_object* v___x_1540_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1531_);
v___x_1540_ = v___x_1536_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1531_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
else
{
lean_object* v_val_1542_; lean_object* v___x_1544_; 
v_val_1542_ = lean_ctor_get(v_fst_1538_, 0);
lean_inc(v_val_1542_);
lean_dec_ref(v_fst_1538_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_val_1542_);
v___x_1544_ = v___x_1536_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_val_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_a_1547_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1533_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1533_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_dec(v_declName_1511_);
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_declName_1511_);
v_a_1556_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1517_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1517_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
return v_res_1570_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1571_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1574_ = lean_box(1);
v___x_1575_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1576_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v___x_1575_);
lean_ctor_set(v___x_1577_, 2, v___x_1574_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___f_1586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1586_, 0, v_declName_1580_);
v___x_1587_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1589_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1587_, v___x_1588_, v___f_1586_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1597_, lean_object* v_as_1598_, lean_object* v_as_x27_1599_, lean_object* v_b_1600_, lean_object* v_a_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1597_, v_as_x27_1599_, v_b_1600_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1608_, lean_object* v_as_1609_, lean_object* v_as_x27_1610_, lean_object* v_b_1611_, lean_object* v_a_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1608_, v_as_1609_, v_as_x27_1610_, v_b_1611_, v_a_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v_as_1609_);
return v_res_1618_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(lean_object* v_opts_1619_, lean_object* v_opt_1620_){
_start:
{
lean_object* v_name_1621_; lean_object* v_defValue_1622_; lean_object* v_map_1623_; lean_object* v___x_1624_; 
v_name_1621_ = lean_ctor_get(v_opt_1620_, 0);
v_defValue_1622_ = lean_ctor_get(v_opt_1620_, 1);
v_map_1623_ = lean_ctor_get(v_opts_1619_, 0);
v___x_1624_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1623_, v_name_1621_);
if (lean_obj_tag(v___x_1624_) == 0)
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_unbox(v_defValue_1622_);
return v___x_1625_;
}
else
{
lean_object* v_val_1626_; 
v_val_1626_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_val_1626_);
lean_dec_ref(v___x_1624_);
if (lean_obj_tag(v_val_1626_) == 1)
{
uint8_t v_v_1627_; 
v_v_1627_ = lean_ctor_get_uint8(v_val_1626_, 0);
lean_dec_ref(v_val_1626_);
return v_v_1627_;
}
else
{
uint8_t v___x_1628_; 
lean_dec(v_val_1626_);
v___x_1628_ = lean_unbox(v_defValue_1622_);
return v___x_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1___boxed(lean_object* v_opts_1629_, lean_object* v_opt_1630_){
_start:
{
uint8_t v_res_1631_; lean_object* v_r_1632_; 
v_res_1631_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_1629_, v_opt_1630_);
lean_dec_ref(v_opt_1630_);
lean_dec_ref(v_opts_1629_);
v_r_1632_ = lean_box(v_res_1631_);
return v_r_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(lean_object* v_opts_1633_, lean_object* v_opt_1634_){
_start:
{
lean_object* v_name_1635_; lean_object* v_defValue_1636_; lean_object* v_map_1637_; lean_object* v___x_1638_; 
v_name_1635_ = lean_ctor_get(v_opt_1634_, 0);
v_defValue_1636_ = lean_ctor_get(v_opt_1634_, 1);
v_map_1637_ = lean_ctor_get(v_opts_1633_, 0);
v___x_1638_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1637_, v_name_1635_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_inc(v_defValue_1636_);
return v_defValue_1636_;
}
else
{
lean_object* v_val_1639_; 
v_val_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_val_1639_);
lean_dec_ref(v___x_1638_);
if (lean_obj_tag(v_val_1639_) == 3)
{
lean_object* v_v_1640_; 
v_v_1640_ = lean_ctor_get(v_val_1639_, 0);
lean_inc(v_v_1640_);
lean_dec_ref(v_val_1639_);
return v_v_1640_;
}
else
{
lean_dec(v_val_1639_);
lean_inc(v_defValue_1636_);
return v_defValue_1636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2___boxed(lean_object* v_opts_1641_, lean_object* v_opt_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_1641_, v_opt_1642_);
lean_dec_ref(v_opt_1642_);
lean_dec_ref(v_opts_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(lean_object* v_o_1647_, lean_object* v_k_1648_, uint8_t v_v_1649_){
_start:
{
lean_object* v_map_1650_; uint8_t v_hasTrace_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1665_; 
v_map_1650_ = lean_ctor_get(v_o_1647_, 0);
v_hasTrace_1651_ = lean_ctor_get_uint8(v_o_1647_, sizeof(void*)*1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_o_1647_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1653_ = v_o_1647_;
v_isShared_1654_ = v_isSharedCheck_1665_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_map_1650_);
lean_dec(v_o_1647_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1665_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1655_, 0, v_v_1649_);
lean_inc(v_k_1648_);
v___x_1656_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1648_, v___x_1655_, v_map_1650_);
if (v_hasTrace_1651_ == 0)
{
lean_object* v___x_1657_; uint8_t v___x_1658_; lean_object* v___x_1660_; 
v___x_1657_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1658_ = l_Lean_Name_isPrefixOf(v___x_1657_, v_k_1648_);
lean_dec(v_k_1648_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1660_ = v___x_1653_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1656_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_ctor_set_uint8(v___x_1660_, sizeof(void*)*1, v___x_1658_);
return v___x_1660_;
}
}
else
{
lean_object* v___x_1663_; 
lean_dec(v_k_1648_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1663_ = v___x_1653_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1656_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*1, v_hasTrace_1651_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___boxed(lean_object* v_o_1666_, lean_object* v_k_1667_, lean_object* v_v_1668_){
_start:
{
uint8_t v_v_boxed_1669_; lean_object* v_res_1670_; 
v_v_boxed_1669_ = lean_unbox(v_v_1668_);
v_res_1670_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_o_1666_, v_k_1667_, v_v_boxed_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(lean_object* v_opts_1671_, lean_object* v_opt_1672_, uint8_t v_val_1673_){
_start:
{
lean_object* v_name_1674_; lean_object* v___x_1675_; 
v_name_1674_ = lean_ctor_get(v_opt_1672_, 0);
lean_inc(v_name_1674_);
lean_dec_ref(v_opt_1672_);
v___x_1675_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_opts_1671_, v_name_1674_, v_val_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object* v_opts_1676_, lean_object* v_opt_1677_, lean_object* v_val_1678_){
_start:
{
uint8_t v_val_boxed_1679_; lean_object* v_res_1680_; 
v_val_boxed_1679_ = lean_unbox(v_val_1678_);
v_res_1680_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_opts_1676_, v_opt_1677_, v_val_boxed_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(lean_object* v_as_1681_, size_t v_i_1682_, size_t v_stop_1683_, lean_object* v_b_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_eq(v_i_1682_, v_stop_1683_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v_defValue_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; size_t v___x_1690_; size_t v___x_1691_; 
v___x_1686_ = lean_array_uget_borrowed(v_as_1681_, v_i_1682_);
v_defValue_1687_ = lean_ctor_get(v___x_1686_, 1);
v___x_1688_ = lean_unbox(v_defValue_1687_);
lean_inc(v___x_1686_);
v___x_1689_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_b_1684_, v___x_1686_, v___x_1688_);
v___x_1690_ = ((size_t)1ULL);
v___x_1691_ = lean_usize_add(v_i_1682_, v___x_1690_);
v_i_1682_ = v___x_1691_;
v_b_1684_ = v___x_1689_;
goto _start;
}
else
{
return v_b_1684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3___boxed(lean_object* v_as_1693_, lean_object* v_i_1694_, lean_object* v_stop_1695_, lean_object* v_b_1696_){
_start:
{
size_t v_i_boxed_1697_; size_t v_stop_boxed_1698_; lean_object* v_res_1699_; 
v_i_boxed_1697_ = lean_unbox_usize(v_i_1694_);
lean_dec(v_i_1694_);
v_stop_boxed_1698_ = lean_unbox_usize(v_stop_1695_);
lean_dec(v_stop_1695_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v_as_1693_, v_i_boxed_1697_, v_stop_boxed_1698_, v_b_1696_);
lean_dec_ref(v_as_1693_);
return v_res_1699_;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1701_ = lean_array_get_size(v___x_1700_);
return v___x_1701_;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1703_ = lean_nat_dec_le(v___x_1702_, v___x_1702_);
return v___x_1703_;
}
}
static size_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1704_; size_t v___x_1705_; 
v___x_1704_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1705_ = lean_usize_of_nat(v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object* v_declName_1706_, lean_object* v___x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v___y_1714_; lean_object* v___y_1715_; lean_object* v_fileName_1716_; lean_object* v_fileMap_1717_; lean_object* v_currRecDepth_1718_; lean_object* v_ref_1719_; lean_object* v_currNamespace_1720_; lean_object* v_openDecls_1721_; lean_object* v_initHeartbeats_1722_; lean_object* v_maxHeartbeats_1723_; lean_object* v_quotContext_1724_; lean_object* v_currMacroScope_1725_; lean_object* v_cancelTk_x3f_1726_; uint8_t v_suppressElabErrors_1727_; lean_object* v_inheritedTraceOptions_1728_; lean_object* v___y_1729_; lean_object* v___x_1734_; lean_object* v_fileName_1735_; lean_object* v_fileMap_1736_; lean_object* v_options_1737_; lean_object* v_currRecDepth_1738_; lean_object* v_ref_1739_; lean_object* v_currNamespace_1740_; lean_object* v_openDecls_1741_; lean_object* v_initHeartbeats_1742_; lean_object* v_maxHeartbeats_1743_; lean_object* v_quotContext_1744_; lean_object* v_currMacroScope_1745_; lean_object* v_cancelTk_x3f_1746_; uint8_t v_suppressElabErrors_1747_; lean_object* v_inheritedTraceOptions_1748_; uint8_t v___y_1750_; lean_object* v___y_1751_; uint8_t v___y_1752_; lean_object* v___y_1774_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1734_ = lean_st_ref_get(v___y_1711_);
v_fileName_1735_ = lean_ctor_get(v___y_1710_, 0);
v_fileMap_1736_ = lean_ctor_get(v___y_1710_, 1);
v_options_1737_ = lean_ctor_get(v___y_1710_, 2);
v_currRecDepth_1738_ = lean_ctor_get(v___y_1710_, 3);
v_ref_1739_ = lean_ctor_get(v___y_1710_, 5);
v_currNamespace_1740_ = lean_ctor_get(v___y_1710_, 6);
v_openDecls_1741_ = lean_ctor_get(v___y_1710_, 7);
v_initHeartbeats_1742_ = lean_ctor_get(v___y_1710_, 8);
v_maxHeartbeats_1743_ = lean_ctor_get(v___y_1710_, 9);
v_quotContext_1744_ = lean_ctor_get(v___y_1710_, 10);
v_currMacroScope_1745_ = lean_ctor_get(v___y_1710_, 11);
v_cancelTk_x3f_1746_ = lean_ctor_get(v___y_1710_, 12);
v_suppressElabErrors_1747_ = lean_ctor_get_uint8(v___y_1710_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1748_ = lean_ctor_get(v___y_1710_, 13);
v___x_1779_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1780_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1781_ = lean_nat_dec_lt(v___x_1707_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_inc_ref(v_options_1737_);
v___y_1774_ = v_options_1737_;
goto v___jp_1773_;
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = lean_uint8_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1);
if (v___x_1782_ == 0)
{
if (v___x_1781_ == 0)
{
lean_inc_ref(v_options_1737_);
v___y_1774_ = v_options_1737_;
goto v___jp_1773_;
}
else
{
size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = ((size_t)0ULL);
v___x_1784_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
lean_inc_ref(v_options_1737_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1779_, v___x_1783_, v___x_1784_, v_options_1737_);
v___y_1774_ = v___x_1785_;
goto v___jp_1773_;
}
}
else
{
size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = ((size_t)0ULL);
v___x_1787_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
lean_inc_ref(v_options_1737_);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1779_, v___x_1786_, v___x_1787_, v_options_1737_);
v___y_1774_ = v___x_1788_;
goto v___jp_1773_;
}
}
v___jp_1713_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = l_Lean_maxRecDepth;
v___x_1731_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v___y_1715_, v___x_1730_);
lean_inc_ref(v_inheritedTraceOptions_1728_);
lean_inc(v_cancelTk_x3f_1726_);
lean_inc(v_currMacroScope_1725_);
lean_inc(v_quotContext_1724_);
lean_inc(v_maxHeartbeats_1723_);
lean_inc(v_initHeartbeats_1722_);
lean_inc(v_openDecls_1721_);
lean_inc(v_currNamespace_1720_);
lean_inc(v_ref_1719_);
lean_inc(v_currRecDepth_1718_);
lean_inc_ref(v_fileMap_1717_);
lean_inc_ref(v_fileName_1716_);
v___x_1732_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1732_, 0, v_fileName_1716_);
lean_ctor_set(v___x_1732_, 1, v_fileMap_1717_);
lean_ctor_set(v___x_1732_, 2, v___y_1715_);
lean_ctor_set(v___x_1732_, 3, v_currRecDepth_1718_);
lean_ctor_set(v___x_1732_, 4, v___x_1731_);
lean_ctor_set(v___x_1732_, 5, v_ref_1719_);
lean_ctor_set(v___x_1732_, 6, v_currNamespace_1720_);
lean_ctor_set(v___x_1732_, 7, v_openDecls_1721_);
lean_ctor_set(v___x_1732_, 8, v_initHeartbeats_1722_);
lean_ctor_set(v___x_1732_, 9, v_maxHeartbeats_1723_);
lean_ctor_set(v___x_1732_, 10, v_quotContext_1724_);
lean_ctor_set(v___x_1732_, 11, v_currMacroScope_1725_);
lean_ctor_set(v___x_1732_, 12, v_cancelTk_x3f_1726_);
lean_ctor_set(v___x_1732_, 13, v_inheritedTraceOptions_1728_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*14, v___y_1714_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*14 + 1, v_suppressElabErrors_1727_);
v___x_1733_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1706_, v___y_1708_, v___y_1709_, v___x_1732_, v___y_1729_);
lean_dec_ref(v___x_1732_);
return v___x_1733_;
}
v___jp_1749_:
{
if (v___y_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v_env_1754_; lean_object* v_nextMacroScope_1755_; lean_object* v_ngen_1756_; lean_object* v_auxDeclNGen_1757_; lean_object* v_traceState_1758_; lean_object* v_messages_1759_; lean_object* v_infoState_1760_; lean_object* v_snapshotTasks_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1771_; 
v___x_1753_ = lean_st_ref_take(v___y_1711_);
v_env_1754_ = lean_ctor_get(v___x_1753_, 0);
v_nextMacroScope_1755_ = lean_ctor_get(v___x_1753_, 1);
v_ngen_1756_ = lean_ctor_get(v___x_1753_, 2);
v_auxDeclNGen_1757_ = lean_ctor_get(v___x_1753_, 3);
v_traceState_1758_ = lean_ctor_get(v___x_1753_, 4);
v_messages_1759_ = lean_ctor_get(v___x_1753_, 6);
v_infoState_1760_ = lean_ctor_get(v___x_1753_, 7);
v_snapshotTasks_1761_ = lean_ctor_get(v___x_1753_, 8);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v___x_1753_, 5);
lean_dec(v_unused_1772_);
v___x_1763_ = v___x_1753_;
v_isShared_1764_ = v_isSharedCheck_1771_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snapshotTasks_1761_);
lean_inc(v_infoState_1760_);
lean_inc(v_messages_1759_);
lean_inc(v_traceState_1758_);
lean_inc(v_auxDeclNGen_1757_);
lean_inc(v_ngen_1756_);
lean_inc(v_nextMacroScope_1755_);
lean_inc(v_env_1754_);
lean_dec(v___x_1753_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1771_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1765_ = l_Lean_Kernel_enableDiag(v_env_1754_, v___y_1750_);
v___x_1766_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 5, v___x_1766_);
lean_ctor_set(v___x_1763_, 0, v___x_1765_);
v___x_1768_ = v___x_1763_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_nextMacroScope_1755_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_ngen_1756_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_auxDeclNGen_1757_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_traceState_1758_);
lean_ctor_set(v_reuseFailAlloc_1770_, 5, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1770_, 6, v_messages_1759_);
lean_ctor_set(v_reuseFailAlloc_1770_, 7, v_infoState_1760_);
lean_ctor_set(v_reuseFailAlloc_1770_, 8, v_snapshotTasks_1761_);
v___x_1768_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_st_ref_set(v___y_1711_, v___x_1768_);
v___y_1714_ = v___y_1750_;
v___y_1715_ = v___y_1751_;
v_fileName_1716_ = v_fileName_1735_;
v_fileMap_1717_ = v_fileMap_1736_;
v_currRecDepth_1718_ = v_currRecDepth_1738_;
v_ref_1719_ = v_ref_1739_;
v_currNamespace_1720_ = v_currNamespace_1740_;
v_openDecls_1721_ = v_openDecls_1741_;
v_initHeartbeats_1722_ = v_initHeartbeats_1742_;
v_maxHeartbeats_1723_ = v_maxHeartbeats_1743_;
v_quotContext_1724_ = v_quotContext_1744_;
v_currMacroScope_1725_ = v_currMacroScope_1745_;
v_cancelTk_x3f_1726_ = v_cancelTk_x3f_1746_;
v_suppressElabErrors_1727_ = v_suppressElabErrors_1747_;
v_inheritedTraceOptions_1728_ = v_inheritedTraceOptions_1748_;
v___y_1729_ = v___y_1711_;
goto v___jp_1713_;
}
}
}
else
{
v___y_1714_ = v___y_1750_;
v___y_1715_ = v___y_1751_;
v_fileName_1716_ = v_fileName_1735_;
v_fileMap_1717_ = v_fileMap_1736_;
v_currRecDepth_1718_ = v_currRecDepth_1738_;
v_ref_1719_ = v_ref_1739_;
v_currNamespace_1720_ = v_currNamespace_1740_;
v_openDecls_1721_ = v_openDecls_1741_;
v_initHeartbeats_1722_ = v_initHeartbeats_1742_;
v_maxHeartbeats_1723_ = v_maxHeartbeats_1743_;
v_quotContext_1724_ = v_quotContext_1744_;
v_currMacroScope_1725_ = v_currMacroScope_1745_;
v_cancelTk_x3f_1726_ = v_cancelTk_x3f_1746_;
v_suppressElabErrors_1727_ = v_suppressElabErrors_1747_;
v_inheritedTraceOptions_1728_ = v_inheritedTraceOptions_1748_;
v___y_1729_ = v___y_1711_;
goto v___jp_1713_;
}
}
v___jp_1773_:
{
lean_object* v_env_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; uint8_t v___x_1778_; 
v_env_1775_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_env_1775_);
lean_dec(v___x_1734_);
v___x_1776_ = l_Lean_diagnostics;
v___x_1777_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___y_1774_, v___x_1776_);
v___x_1778_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1775_);
lean_dec_ref(v_env_1775_);
if (v___x_1778_ == 0)
{
if (v___x_1777_ == 0)
{
v___y_1714_ = v___x_1777_;
v___y_1715_ = v___y_1774_;
v_fileName_1716_ = v_fileName_1735_;
v_fileMap_1717_ = v_fileMap_1736_;
v_currRecDepth_1718_ = v_currRecDepth_1738_;
v_ref_1719_ = v_ref_1739_;
v_currNamespace_1720_ = v_currNamespace_1740_;
v_openDecls_1721_ = v_openDecls_1741_;
v_initHeartbeats_1722_ = v_initHeartbeats_1742_;
v_maxHeartbeats_1723_ = v_maxHeartbeats_1743_;
v_quotContext_1724_ = v_quotContext_1744_;
v_currMacroScope_1725_ = v_currMacroScope_1745_;
v_cancelTk_x3f_1726_ = v_cancelTk_x3f_1746_;
v_suppressElabErrors_1727_ = v_suppressElabErrors_1747_;
v_inheritedTraceOptions_1728_ = v_inheritedTraceOptions_1748_;
v___y_1729_ = v___y_1711_;
goto v___jp_1713_;
}
else
{
v___y_1750_ = v___x_1777_;
v___y_1751_ = v___y_1774_;
v___y_1752_ = v___x_1778_;
goto v___jp_1749_;
}
}
else
{
v___y_1750_ = v___x_1777_;
v___y_1751_ = v___y_1774_;
v___y_1752_ = v___x_1777_;
goto v___jp_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object* v_declName_1789_, lean_object* v___x_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Meta_getEqnsFor_x3f___lam__0(v_declName_1789_, v___x_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___x_1790_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1803_ = lean_unsigned_to_nat(32u);
v___x_1804_ = lean_mk_empty_array_with_capacity(v___x_1803_);
lean_dec_ref(v___x_1804_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1806_, 0, v_declName_1797_);
lean_closure_set(v___f_1806_, 1, v___x_1805_);
v___x_1807_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1808_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1809_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1807_, v___x_1808_, v___f_1806_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(lean_object* v_msgData_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v_env_1824_; lean_object* v___x_1825_; lean_object* v_mctx_1826_; lean_object* v_lctx_1827_; lean_object* v_options_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1823_ = lean_st_ref_get(v___y_1821_);
v_env_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc_ref(v_env_1824_);
lean_dec(v___x_1823_);
v___x_1825_ = lean_st_ref_get(v___y_1819_);
v_mctx_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref(v_mctx_1826_);
lean_dec(v___x_1825_);
v_lctx_1827_ = lean_ctor_get(v___y_1818_, 2);
v_options_1828_ = lean_ctor_get(v___y_1820_, 2);
lean_inc_ref(v_options_1828_);
lean_inc_ref(v_lctx_1827_);
v___x_1829_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1829_, 0, v_env_1824_);
lean_ctor_set(v___x_1829_, 1, v_mctx_1826_);
lean_ctor_set(v___x_1829_, 2, v_lctx_1827_);
lean_ctor_set(v___x_1829_, 3, v_options_1828_);
v___x_1830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v_msgData_1817_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1___boxed(lean_object* v_msgData_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msgData_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1839_; double v___x_1840_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_float_of_nat(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(lean_object* v_cls_1844_, lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_ref_1851_; lean_object* v___x_1852_; lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1897_; 
v_ref_1851_ = lean_ctor_get(v___y_1848_, 5);
v___x_1852_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msg_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1897_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1897_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v_traceState_1858_; lean_object* v_env_1859_; lean_object* v_nextMacroScope_1860_; lean_object* v_ngen_1861_; lean_object* v_auxDeclNGen_1862_; lean_object* v_cache_1863_; lean_object* v_messages_1864_; lean_object* v_infoState_1865_; lean_object* v_snapshotTasks_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1896_; 
v___x_1857_ = lean_st_ref_take(v___y_1849_);
v_traceState_1858_ = lean_ctor_get(v___x_1857_, 4);
v_env_1859_ = lean_ctor_get(v___x_1857_, 0);
v_nextMacroScope_1860_ = lean_ctor_get(v___x_1857_, 1);
v_ngen_1861_ = lean_ctor_get(v___x_1857_, 2);
v_auxDeclNGen_1862_ = lean_ctor_get(v___x_1857_, 3);
v_cache_1863_ = lean_ctor_get(v___x_1857_, 5);
v_messages_1864_ = lean_ctor_get(v___x_1857_, 6);
v_infoState_1865_ = lean_ctor_get(v___x_1857_, 7);
v_snapshotTasks_1866_ = lean_ctor_get(v___x_1857_, 8);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1868_ = v___x_1857_;
v_isShared_1869_ = v_isSharedCheck_1896_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_snapshotTasks_1866_);
lean_inc(v_infoState_1865_);
lean_inc(v_messages_1864_);
lean_inc(v_cache_1863_);
lean_inc(v_traceState_1858_);
lean_inc(v_auxDeclNGen_1862_);
lean_inc(v_ngen_1861_);
lean_inc(v_nextMacroScope_1860_);
lean_inc(v_env_1859_);
lean_dec(v___x_1857_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1896_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
uint64_t v_tid_1870_; lean_object* v_traces_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1895_; 
v_tid_1870_ = lean_ctor_get_uint64(v_traceState_1858_, sizeof(void*)*1);
v_traces_1871_ = lean_ctor_get(v_traceState_1858_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_traceState_1858_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1873_ = v_traceState_1858_;
v_isShared_1874_ = v_isSharedCheck_1895_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_traces_1871_);
lean_dec(v_traceState_1858_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1895_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; double v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0);
v___x_1877_ = 0;
v___x_1878_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1));
v___x_1879_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1879_, 0, v_cls_1844_);
lean_ctor_set(v___x_1879_, 1, v___x_1875_);
lean_ctor_set(v___x_1879_, 2, v___x_1878_);
lean_ctor_set_float(v___x_1879_, sizeof(void*)*3, v___x_1876_);
lean_ctor_set_float(v___x_1879_, sizeof(void*)*3 + 8, v___x_1876_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*3 + 16, v___x_1877_);
v___x_1880_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__2));
v___x_1881_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v_a_1853_);
lean_ctor_set(v___x_1881_, 2, v___x_1880_);
lean_inc(v_ref_1851_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_ref_1851_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lean_PersistentArray_push___redArg(v_traces_1871_, v___x_1882_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1883_);
v___x_1885_ = v___x_1873_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1883_);
lean_ctor_set_uint64(v_reuseFailAlloc_1894_, sizeof(void*)*1, v_tid_1870_);
v___x_1885_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 4, v___x_1885_);
v___x_1887_ = v___x_1868_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_env_1859_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_nextMacroScope_1860_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_ngen_1861_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_auxDeclNGen_1862_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1893_, 5, v_cache_1863_);
lean_ctor_set(v_reuseFailAlloc_1893_, 6, v_messages_1864_);
lean_ctor_set(v_reuseFailAlloc_1893_, 7, v_infoState_1865_);
lean_ctor_set(v_reuseFailAlloc_1893_, 8, v_snapshotTasks_1866_);
v___x_1887_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_st_ref_set(v___y_1849_, v___x_1887_);
v___x_1889_ = lean_box(0);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1889_);
v___x_1891_ = v___x_1855_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___boxed(lean_object* v_cls_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(v_cls_1898_, v_msg_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(lean_object* v___x_1906_, lean_object* v_as_1907_, size_t v_i_1908_, size_t v_stop_1909_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_usize_dec_eq(v_i_1908_, v_stop_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v_defValue_1912_; uint8_t v___x_1913_; uint8_t v___y_1919_; uint8_t v___x_1920_; 
v___x_1911_ = lean_array_uget_borrowed(v_as_1907_, v_i_1908_);
v_defValue_1912_ = lean_ctor_get(v___x_1911_, 1);
v___x_1913_ = 1;
v___x_1920_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___x_1906_, v___x_1911_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; 
v___x_1921_ = lean_unbox(v_defValue_1912_);
if (v___x_1921_ == 0)
{
goto v___jp_1914_;
}
else
{
v___y_1919_ = v___x_1920_;
goto v___jp_1918_;
}
}
else
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_unbox(v_defValue_1912_);
v___y_1919_ = v___x_1922_;
goto v___jp_1918_;
}
v___jp_1914_:
{
if (v___x_1910_ == 0)
{
size_t v___x_1915_; size_t v___x_1916_; 
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_add(v_i_1908_, v___x_1915_);
v_i_1908_ = v___x_1916_;
goto _start;
}
else
{
return v___x_1913_;
}
}
v___jp_1918_:
{
if (v___y_1919_ == 0)
{
return v___x_1913_;
}
else
{
goto v___jp_1914_;
}
}
}
else
{
uint8_t v___x_1923_; 
v___x_1923_ = 0;
return v___x_1923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object* v___x_1924_, lean_object* v_as_1925_, lean_object* v_i_1926_, lean_object* v_stop_1927_){
_start:
{
size_t v_i_boxed_1928_; size_t v_stop_boxed_1929_; uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_i_boxed_1928_ = lean_unbox_usize(v_i_1926_);
lean_dec(v_i_1926_);
v_stop_boxed_1929_ = lean_unbox_usize(v_stop_1927_);
lean_dec(v_stop_1927_);
v_res_1930_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v___x_1924_, v_as_1925_, v_i_boxed_1928_, v_stop_boxed_1929_);
lean_dec_ref(v_as_1925_);
lean_dec_ref(v___x_1924_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
static uint8_t _init_l_Lean_Meta_generateEagerEqns___closed__0(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1932_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_nat_dec_lt(v___x_1933_, v___x_1932_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__4(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_1942_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1943_ = l_Lean_Name_append(v___x_1942_, v___x_1941_);
return v___x_1943_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__6(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__5));
v___x_1946_ = l_Lean_stringToMessageData(v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object* v_declName_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1980_ = lean_uint8_once(&l_Lean_Meta_generateEagerEqns___closed__0, &l_Lean_Meta_generateEagerEqns___closed__0_once, _init_l_Lean_Meta_generateEagerEqns___closed__0);
if (v___x_1980_ == 0)
{
lean_dec(v_declName_1947_);
goto v___jp_1953_;
}
else
{
if (v___x_1980_ == 0)
{
lean_dec(v_declName_1947_);
goto v___jp_1953_;
}
else
{
lean_object* v_options_1981_; lean_object* v_inheritedTraceOptions_1982_; size_t v___x_1983_; size_t v___x_1984_; uint8_t v___x_1985_; 
v_options_1981_ = lean_ctor_get(v_a_1950_, 2);
v_inheritedTraceOptions_1982_ = lean_ctor_get(v_a_1950_, 13);
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v_options_1981_, v___x_1979_, v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_dec(v_declName_1947_);
goto v___jp_1953_;
}
else
{
uint8_t v_hasTrace_1986_; 
v_hasTrace_1986_ = lean_ctor_get_uint8(v_options_1981_, sizeof(void*)*1);
if (v_hasTrace_1986_ == 0)
{
v___y_1957_ = v_a_1948_;
v___y_1958_ = v_a_1949_;
v___y_1959_ = v_a_1950_;
v___y_1960_ = v_a_1951_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1987_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_1988_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__4, &l_Lean_Meta_generateEagerEqns___closed__4_once, _init_l_Lean_Meta_generateEagerEqns___closed__4);
v___x_1989_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1982_, v_options_1981_, v___x_1988_);
if (v___x_1989_ == 0)
{
v___y_1957_ = v_a_1948_;
v___y_1958_ = v_a_1949_;
v___y_1959_ = v_a_1950_;
v___y_1960_ = v_a_1951_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1990_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__6, &l_Lean_Meta_generateEagerEqns___closed__6_once, _init_l_Lean_Meta_generateEagerEqns___closed__6);
lean_inc(v_declName_1947_);
v___x_1991_ = l_Lean_MessageData_ofName(v_declName_1947_);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(v___x_1987_, v___x_1992_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_dec_ref(v___x_1993_);
v___y_1957_ = v_a_1948_;
v___y_1958_ = v_a_1949_;
v___y_1959_ = v_a_1950_;
v___y_1960_ = v_a_1951_;
goto v___jp_1956_;
}
else
{
lean_dec(v_declName_1947_);
return v___x_1993_;
}
}
}
}
}
}
v___jp_1953_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
v___jp_1956_:
{
lean_object* v___x_1961_; 
v___x_1961_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1947_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1961_, 0);
lean_dec(v_unused_1970_);
v___x_1963_ = v___x_1961_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_dec(v___x_1961_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_box(0);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
v_a_1971_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1961_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1961_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___boxed(lean_object* v_declName_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Meta_generateEagerEqns(v_declName_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_st_mk_ref(v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2007_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2026_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2026_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2026_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_unbox(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
lean_dec_ref(v_f_2007_);
v___x_2015_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 1);
lean_ctor_set(v___x_2012_, 0, v___x_2015_);
v___x_2017_ = v___x_2012_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2019_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2020_ = lean_st_ref_take(v___x_2019_);
v___x_2021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_f_2007_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_st_ref_set(v___x_2019_, v___x_2021_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2022_);
v___x_2024_ = v___x_2012_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v_f_2007_);
v_a_2027_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2009_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2009_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2041_, lean_object* v_as_x27_2042_, lean_object* v_b_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
if (lean_obj_tag(v_as_x27_2042_) == 0)
{
lean_object* v___x_2049_; 
lean_dec(v_declName_2041_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_b_2043_);
return v___x_2049_;
}
else
{
lean_object* v_head_2050_; lean_object* v_tail_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_b_2043_);
v_head_2050_ = lean_ctor_get(v_as_x27_2042_, 0);
v_tail_2051_ = lean_ctor_get(v_as_x27_2042_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_as_x27_2042_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2053_ = v_as_x27_2042_;
v_isShared_2054_ = v_isSharedCheck_2079_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_tail_2051_);
lean_inc(v_head_2050_);
lean_dec(v_as_x27_2042_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2079_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; 
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
lean_inc(v_declName_2041_);
v___x_2055_ = lean_apply_6(v_head_2050_, v_declName_2041_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, lean_box(0));
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2070_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2070_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2070_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_box(0);
if (lean_obj_tag(v_a_2056_) == 1)
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
lean_dec(v_tail_2051_);
lean_dec(v_declName_2041_);
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_a_2056_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 0);
lean_ctor_set(v___x_2053_, 1, v___x_2060_);
lean_ctor_set(v___x_2053_, 0, v___x_2061_);
v___x_2063_ = v___x_2053_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2060_);
v___x_2063_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2065_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2063_);
v___x_2065_ = v___x_2058_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_object* v___x_2068_; 
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_del_object(v___x_2053_);
v___x_2068_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2042_ = v_tail_2051_;
v_b_2043_ = v___x_2068_;
goto _start;
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_del_object(v___x_2053_);
lean_dec(v_tail_2051_);
lean_dec(v_declName_2041_);
v_a_2071_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2055_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2055_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2080_, lean_object* v_as_x27_2081_, lean_object* v_b_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2080_, v_as_x27_2081_, v_b_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2089_, lean_object* v_declName_2090_, uint8_t v_nonRec_2091_, lean_object* v___x_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2101_; lean_object* v_env_2102_; uint8_t v___x_2103_; uint8_t v___x_2104_; 
v___x_2101_ = lean_st_ref_get(v___y_2096_);
v_env_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc_ref(v_env_2102_);
lean_dec(v___x_2101_);
v___x_2103_ = 1;
lean_inc(v___x_2089_);
v___x_2104_ = l_Lean_Environment_contains(v_env_2102_, v___x_2089_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_dec(v___x_2089_);
lean_inc(v_declName_2090_);
v___x_2105_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2090_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; uint8_t v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v___x_2107_ = lean_unbox(v_a_2106_);
lean_dec(v_a_2106_);
if (v___x_2107_ == 0)
{
lean_dec_ref(v___x_2092_);
lean_dec(v_declName_2090_);
goto v___jp_2098_;
}
else
{
lean_object* v___x_2108_; 
lean_inc(v_declName_2090_);
v___x_2108_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2090_, v___y_2096_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; uint8_t v___x_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
v___x_2110_ = lean_unbox(v_a_2109_);
lean_dec(v_a_2109_);
if (v___x_2110_ == 0)
{
if (v_nonRec_2091_ == 0)
{
lean_dec_ref(v___x_2092_);
lean_dec(v_declName_2090_);
goto v___jp_2098_;
}
else
{
lean_object* v___x_2111_; lean_object* v_env_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2111_ = lean_st_ref_get(v___y_2096_);
v_env_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_env_2112_);
lean_dec(v___x_2111_);
lean_inc(v_declName_2090_);
v___x_2113_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2112_, v_declName_2090_, v___x_2092_);
v___x_2114_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2090_, v___x_2113_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
return v___x_2114_;
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec_ref(v___x_2092_);
v___x_2115_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2116_ = lean_st_ref_get(v___x_2115_);
v___x_2117_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2118_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2090_, v___x_2116_, v___x_2117_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2128_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2128_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2128_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_fst_2123_; 
v_fst_2123_ = lean_ctor_get(v_a_2119_, 0);
lean_inc(v_fst_2123_);
lean_dec(v_a_2119_);
if (lean_obj_tag(v_fst_2123_) == 0)
{
lean_del_object(v___x_2121_);
goto v___jp_2098_;
}
else
{
lean_object* v_val_2124_; lean_object* v___x_2126_; 
v_val_2124_ = lean_ctor_get(v_fst_2123_, 0);
lean_inc(v_val_2124_);
lean_dec_ref(v_fst_2123_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v_val_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_val_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
v_a_2129_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2118_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2118_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v___x_2092_);
lean_dec(v_declName_2090_);
v_a_2137_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2108_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2108_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v___x_2092_);
lean_dec(v_declName_2090_);
v_a_2145_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2105_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2105_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v___x_2092_);
lean_dec(v_declName_2090_);
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2089_);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
return v___x_2154_;
}
v___jp_2098_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2155_, lean_object* v_declName_2156_, lean_object* v_nonRec_2157_, lean_object* v___x_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
uint8_t v_nonRec_boxed_2164_; lean_object* v_res_2165_; 
v_nonRec_boxed_2164_ = lean_unbox(v_nonRec_2157_);
v_res_2165_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2155_, v_declName_2156_, v_nonRec_boxed_2164_, v___x_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_ref_2172_; lean_object* v___x_2173_; lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2182_; 
v_ref_2172_ = lean_ctor_get(v___y_2169_, 5);
v___x_2173_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msg_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2182_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2182_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_inc(v_ref_2172_);
v___x_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_ref_2172_);
lean_ctor_set(v___x_2178_, 1, v_a_2174_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 1);
lean_ctor_set(v___x_2176_, 0, v___x_2178_);
v___x_2180_ = v___x_2176_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2190_, uint8_t v_isExporting_2191_, lean_object* v___x_2192_, lean_object* v___y_2193_, lean_object* v___x_2194_, lean_object* v_a_x3f_2195_){
_start:
{
lean_object* v___x_2197_; lean_object* v_env_2198_; lean_object* v_nextMacroScope_2199_; lean_object* v_ngen_2200_; lean_object* v_auxDeclNGen_2201_; lean_object* v_traceState_2202_; lean_object* v_messages_2203_; lean_object* v_infoState_2204_; lean_object* v_snapshotTasks_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2230_; 
v___x_2197_ = lean_st_ref_take(v___y_2190_);
v_env_2198_ = lean_ctor_get(v___x_2197_, 0);
v_nextMacroScope_2199_ = lean_ctor_get(v___x_2197_, 1);
v_ngen_2200_ = lean_ctor_get(v___x_2197_, 2);
v_auxDeclNGen_2201_ = lean_ctor_get(v___x_2197_, 3);
v_traceState_2202_ = lean_ctor_get(v___x_2197_, 4);
v_messages_2203_ = lean_ctor_get(v___x_2197_, 6);
v_infoState_2204_ = lean_ctor_get(v___x_2197_, 7);
v_snapshotTasks_2205_ = lean_ctor_get(v___x_2197_, 8);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2197_, 5);
lean_dec(v_unused_2231_);
v___x_2207_ = v___x_2197_;
v_isShared_2208_ = v_isSharedCheck_2230_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_snapshotTasks_2205_);
lean_inc(v_infoState_2204_);
lean_inc(v_messages_2203_);
lean_inc(v_traceState_2202_);
lean_inc(v_auxDeclNGen_2201_);
lean_inc(v_ngen_2200_);
lean_inc(v_nextMacroScope_2199_);
lean_inc(v_env_2198_);
lean_dec(v___x_2197_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2230_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = l_Lean_Environment_setExporting(v_env_2198_, v_isExporting_2191_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 5, v___x_2192_);
lean_ctor_set(v___x_2207_, 0, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_nextMacroScope_2199_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_ngen_2200_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_auxDeclNGen_2201_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_traceState_2202_);
lean_ctor_set(v_reuseFailAlloc_2229_, 5, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2229_, 6, v_messages_2203_);
lean_ctor_set(v_reuseFailAlloc_2229_, 7, v_infoState_2204_);
lean_ctor_set(v_reuseFailAlloc_2229_, 8, v_snapshotTasks_2205_);
v___x_2211_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v_mctx_2214_; lean_object* v_zetaDeltaFVarIds_2215_; lean_object* v_postponed_2216_; lean_object* v_diag_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2227_; 
v___x_2212_ = lean_st_ref_set(v___y_2190_, v___x_2211_);
v___x_2213_ = lean_st_ref_take(v___y_2193_);
v_mctx_2214_ = lean_ctor_get(v___x_2213_, 0);
v_zetaDeltaFVarIds_2215_ = lean_ctor_get(v___x_2213_, 2);
v_postponed_2216_ = lean_ctor_get(v___x_2213_, 3);
v_diag_2217_ = lean_ctor_get(v___x_2213_, 4);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v___x_2213_, 1);
lean_dec(v_unused_2228_);
v___x_2219_ = v___x_2213_;
v_isShared_2220_ = v_isSharedCheck_2227_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_diag_2217_);
lean_inc(v_postponed_2216_);
lean_inc(v_zetaDeltaFVarIds_2215_);
lean_inc(v_mctx_2214_);
lean_dec(v___x_2213_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2227_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v___x_2194_);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_mctx_2214_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_zetaDeltaFVarIds_2215_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_postponed_2216_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_diag_2217_);
v___x_2222_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_st_ref_set(v___y_2193_, v___x_2222_);
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2232_, lean_object* v_isExporting_2233_, lean_object* v___x_2234_, lean_object* v___y_2235_, lean_object* v___x_2236_, lean_object* v_a_x3f_2237_, lean_object* v___y_2238_){
_start:
{
uint8_t v_isExporting_boxed_2239_; lean_object* v_res_2240_; 
v_isExporting_boxed_2239_ = lean_unbox(v_isExporting_2233_);
v_res_2240_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2232_, v_isExporting_boxed_2239_, v___x_2234_, v___y_2235_, v___x_2236_, v_a_x3f_2237_);
lean_dec(v_a_x3f_2237_);
lean_dec(v___y_2235_);
lean_dec(v___y_2232_);
return v_res_2240_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_2242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
lean_ctor_set(v___x_2242_, 2, v___x_2241_);
lean_ctor_set(v___x_2242_, 3, v___x_2241_);
lean_ctor_set(v___x_2242_, 4, v___x_2241_);
lean_ctor_set(v___x_2242_, 5, v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2243_, uint8_t v_isExporting_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v_env_2251_; uint8_t v_isExporting_2252_; lean_object* v___x_2253_; lean_object* v_env_2254_; lean_object* v_nextMacroScope_2255_; lean_object* v_ngen_2256_; lean_object* v_auxDeclNGen_2257_; lean_object* v_traceState_2258_; lean_object* v_messages_2259_; lean_object* v_infoState_2260_; lean_object* v_snapshotTasks_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2315_; 
v___x_2250_ = lean_st_ref_get(v___y_2248_);
v_env_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref(v_env_2251_);
lean_dec(v___x_2250_);
v_isExporting_2252_ = lean_ctor_get_uint8(v_env_2251_, sizeof(void*)*8);
lean_dec_ref(v_env_2251_);
v___x_2253_ = lean_st_ref_take(v___y_2248_);
v_env_2254_ = lean_ctor_get(v___x_2253_, 0);
v_nextMacroScope_2255_ = lean_ctor_get(v___x_2253_, 1);
v_ngen_2256_ = lean_ctor_get(v___x_2253_, 2);
v_auxDeclNGen_2257_ = lean_ctor_get(v___x_2253_, 3);
v_traceState_2258_ = lean_ctor_get(v___x_2253_, 4);
v_messages_2259_ = lean_ctor_get(v___x_2253_, 6);
v_infoState_2260_ = lean_ctor_get(v___x_2253_, 7);
v_snapshotTasks_2261_ = lean_ctor_get(v___x_2253_, 8);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v___x_2253_, 5);
lean_dec(v_unused_2316_);
v___x_2263_ = v___x_2253_;
v_isShared_2264_ = v_isSharedCheck_2315_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_snapshotTasks_2261_);
lean_inc(v_infoState_2260_);
lean_inc(v_messages_2259_);
lean_inc(v_traceState_2258_);
lean_inc(v_auxDeclNGen_2257_);
lean_inc(v_ngen_2256_);
lean_inc(v_nextMacroScope_2255_);
lean_inc(v_env_2254_);
lean_dec(v___x_2253_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2315_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2265_ = l_Lean_Environment_setExporting(v_env_2254_, v_isExporting_2244_);
v___x_2266_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 5, v___x_2266_);
lean_ctor_set(v___x_2263_, 0, v___x_2265_);
v___x_2268_ = v___x_2263_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_nextMacroScope_2255_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_ngen_2256_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_auxDeclNGen_2257_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_traceState_2258_);
lean_ctor_set(v_reuseFailAlloc_2314_, 5, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2314_, 6, v_messages_2259_);
lean_ctor_set(v_reuseFailAlloc_2314_, 7, v_infoState_2260_);
lean_ctor_set(v_reuseFailAlloc_2314_, 8, v_snapshotTasks_2261_);
v___x_2268_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_mctx_2271_; lean_object* v_zetaDeltaFVarIds_2272_; lean_object* v_postponed_2273_; lean_object* v_diag_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2312_; 
v___x_2269_ = lean_st_ref_set(v___y_2248_, v___x_2268_);
v___x_2270_ = lean_st_ref_take(v___y_2246_);
v_mctx_2271_ = lean_ctor_get(v___x_2270_, 0);
v_zetaDeltaFVarIds_2272_ = lean_ctor_get(v___x_2270_, 2);
v_postponed_2273_ = lean_ctor_get(v___x_2270_, 3);
v_diag_2274_ = lean_ctor_get(v___x_2270_, 4);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v___x_2270_, 1);
lean_dec(v_unused_2313_);
v___x_2276_ = v___x_2270_;
v_isShared_2277_ = v_isSharedCheck_2312_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_diag_2274_);
lean_inc(v_postponed_2273_);
lean_inc(v_zetaDeltaFVarIds_2272_);
lean_inc(v_mctx_2271_);
lean_dec(v___x_2270_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2312_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 1, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_mctx_2271_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_zetaDeltaFVarIds_2272_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_postponed_2273_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_diag_2274_);
v___x_2280_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2281_; lean_object* v_r_2282_; 
v___x_2281_ = lean_st_ref_set(v___y_2246_, v___x_2280_);
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2245_);
v_r_2282_ = lean_apply_5(v_x_2243_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, lean_box(0));
if (lean_obj_tag(v_r_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2299_; 
v_a_2283_ = lean_ctor_get(v_r_2282_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_r_2282_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2285_ = v_r_2282_;
v_isShared_2286_ = v_isSharedCheck_2299_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v_r_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2299_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
lean_inc(v_a_2283_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set_tag(v___x_2285_, 1);
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v___x_2289_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2248_, v_isExporting_2252_, v___x_2266_, v___y_2246_, v___x_2278_, v___x_2288_);
lean_dec_ref(v___x_2288_);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; 
v_unused_2297_ = lean_ctor_get(v___x_2289_, 0);
lean_dec(v_unused_2297_);
v___x_2291_ = v___x_2289_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_dec(v___x_2289_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v_a_2283_);
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2283_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_a_2300_ = lean_ctor_get(v_r_2282_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v_r_2282_);
v___x_2301_ = lean_box(0);
v___x_2302_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2248_, v_isExporting_2252_, v___x_2266_, v___y_2246_, v___x_2278_, v___x_2301_);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v___x_2302_, 0);
lean_dec(v_unused_2310_);
v___x_2304_ = v___x_2302_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v___x_2302_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set_tag(v___x_2304_, 1);
lean_ctor_set(v___x_2304_, 0, v_a_2300_);
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2300_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2317_, lean_object* v_isExporting_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
uint8_t v_isExporting_boxed_2324_; lean_object* v_res_2325_; 
v_isExporting_boxed_2324_ = lean_unbox(v_isExporting_2318_);
v_res_2325_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2317_, v_isExporting_boxed_2324_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2326_, uint8_t v_when_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
if (v_when_2327_ == 0)
{
lean_object* v___x_2333_; 
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
v___x_2333_ = lean_apply_5(v_x_2326_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, lean_box(0));
return v___x_2333_;
}
else
{
uint8_t v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = 0;
v___x_2335_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2326_, v___x_2334_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2336_, lean_object* v_when_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
uint8_t v_when_boxed_2343_; lean_object* v_res_2344_; 
v_when_boxed_2343_ = lean_unbox(v_when_2337_);
v_res_2344_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2336_, v_when_boxed_2343_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
return v_res_2344_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2350_ = l_Lean_stringToMessageData(v___x_2349_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2353_ = l_Lean_stringToMessageData(v___x_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2354_, uint8_t v_nonRec_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; lean_object* v_env_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___f_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; 
v___x_2361_ = lean_st_ref_get(v___y_2359_);
v_env_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc_ref(v_env_2362_);
lean_dec(v___x_2361_);
v___x_2363_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2354_);
v___x_2364_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2362_, v_declName_2354_, v___x_2363_);
v___x_2365_ = lean_box(v_nonRec_2355_);
lean_inc(v___x_2364_);
v___f_2366_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2366_, 0, v___x_2364_);
lean_closure_set(v___f_2366_, 1, v_declName_2354_);
lean_closure_set(v___f_2366_, 2, v___x_2365_);
lean_closure_set(v___f_2366_, 3, v___x_2363_);
v___x_2367_ = 1;
v___x_2368_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2366_, v___x_2367_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
if (lean_obj_tag(v_a_2369_) == 1)
{
lean_object* v_val_2370_; uint8_t v___x_2371_; 
v_val_2370_ = lean_ctor_get(v_a_2369_, 0);
lean_inc(v_val_2370_);
lean_dec_ref(v_a_2369_);
v___x_2371_ = lean_name_eq(v_val_2370_, v___x_2364_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v___x_2368_);
v___x_2372_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2373_ = l_Lean_MessageData_ofName(v_val_2370_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = l_Lean_MessageData_ofName(v___x_2364_);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2380_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
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
else
{
lean_dec(v_val_2370_);
lean_dec(v___x_2364_);
return v___x_2368_;
}
}
else
{
lean_dec(v_a_2369_);
lean_dec(v___x_2364_);
return v___x_2368_;
}
}
else
{
lean_dec(v___x_2364_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2390_, lean_object* v_nonRec_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
uint8_t v_nonRec_boxed_2397_; lean_object* v_res_2398_; 
v_nonRec_boxed_2397_ = lean_unbox(v_nonRec_2391_);
v_res_2398_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2390_, v_nonRec_boxed_2397_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2399_, uint8_t v_nonRec_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2406_ = lean_box(v_nonRec_2400_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2407_, 0, v_declName_2399_);
lean_closure_set(v___f_2407_, 1, v___x_2406_);
v___x_2408_ = lean_unsigned_to_nat(32u);
v___x_2409_ = lean_mk_empty_array_with_capacity(v___x_2408_);
lean_dec_ref(v___x_2409_);
v___x_2410_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2411_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2412_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2410_, v___x_2411_, v___f_2407_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2413_, lean_object* v_nonRec_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
uint8_t v_nonRec_boxed_2420_; lean_object* v_res_2421_; 
v_nonRec_boxed_2420_ = lean_unbox(v_nonRec_2414_);
v_res_2421_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2413_, v_nonRec_boxed_2420_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2422_, lean_object* v_as_2423_, lean_object* v_as_x27_2424_, lean_object* v_b_2425_, lean_object* v_a_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2422_, v_as_x27_2424_, v_b_2425_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2433_, lean_object* v_as_2434_, lean_object* v_as_x27_2435_, lean_object* v_b_2436_, lean_object* v_a_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2433_, v_as_2434_, v_as_x27_2435_, v_b_2436_, v_a_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v_as_2434_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2444_, lean_object* v_x_2445_, uint8_t v_isExporting_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2445_, v_isExporting_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_x_2454_, lean_object* v_isExporting_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v_isExporting_boxed_2461_; lean_object* v_res_2462_; 
v_isExporting_boxed_2461_ = lean_unbox(v_isExporting_2455_);
v_res_2462_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2453_, v_x_2454_, v_isExporting_boxed_2461_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2463_, lean_object* v_x_2464_, uint8_t v_when_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2464_, v_when_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_x_2473_, lean_object* v_when_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
uint8_t v_when_boxed_2480_; lean_object* v_res_2481_; 
v_when_boxed_2480_ = lean_unbox(v_when_2474_);
v_res_2481_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2472_, v_x_2473_, v_when_boxed_2480_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2482_, lean_object* v_msg_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2490_, lean_object* v_msg_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2490_, v_msg_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2497_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = lean_unsigned_to_nat(32u);
v___x_2499_ = lean_mk_empty_array_with_capacity(v___x_2498_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2501_ = ((size_t)5ULL);
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = lean_unsigned_to_nat(32u);
v___x_2504_ = lean_mk_empty_array_with_capacity(v___x_2503_);
v___x_2505_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2506_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2504_);
lean_ctor_set(v___x_2506_, 2, v___x_2502_);
lean_ctor_set(v___x_2506_, 3, v___x_2502_);
lean_ctor_set_usize(v___x_2506_, 4, v___x_2501_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; lean_object* v_traceState_2510_; lean_object* v_traces_2511_; lean_object* v___x_2512_; lean_object* v_traceState_2513_; lean_object* v_env_2514_; lean_object* v_nextMacroScope_2515_; lean_object* v_ngen_2516_; lean_object* v_auxDeclNGen_2517_; lean_object* v_cache_2518_; lean_object* v_messages_2519_; lean_object* v_infoState_2520_; lean_object* v_snapshotTasks_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2540_; 
v___x_2509_ = lean_st_ref_get(v___y_2507_);
v_traceState_2510_ = lean_ctor_get(v___x_2509_, 4);
lean_inc_ref(v_traceState_2510_);
lean_dec(v___x_2509_);
v_traces_2511_ = lean_ctor_get(v_traceState_2510_, 0);
lean_inc_ref(v_traces_2511_);
lean_dec_ref(v_traceState_2510_);
v___x_2512_ = lean_st_ref_take(v___y_2507_);
v_traceState_2513_ = lean_ctor_get(v___x_2512_, 4);
v_env_2514_ = lean_ctor_get(v___x_2512_, 0);
v_nextMacroScope_2515_ = lean_ctor_get(v___x_2512_, 1);
v_ngen_2516_ = lean_ctor_get(v___x_2512_, 2);
v_auxDeclNGen_2517_ = lean_ctor_get(v___x_2512_, 3);
v_cache_2518_ = lean_ctor_get(v___x_2512_, 5);
v_messages_2519_ = lean_ctor_get(v___x_2512_, 6);
v_infoState_2520_ = lean_ctor_get(v___x_2512_, 7);
v_snapshotTasks_2521_ = lean_ctor_get(v___x_2512_, 8);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2523_ = v___x_2512_;
v_isShared_2524_ = v_isSharedCheck_2540_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_snapshotTasks_2521_);
lean_inc(v_infoState_2520_);
lean_inc(v_messages_2519_);
lean_inc(v_cache_2518_);
lean_inc(v_traceState_2513_);
lean_inc(v_auxDeclNGen_2517_);
lean_inc(v_ngen_2516_);
lean_inc(v_nextMacroScope_2515_);
lean_inc(v_env_2514_);
lean_dec(v___x_2512_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2540_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
uint64_t v_tid_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2538_; 
v_tid_2525_ = lean_ctor_get_uint64(v_traceState_2513_, sizeof(void*)*1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_traceState_2513_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v_traceState_2513_, 0);
lean_dec(v_unused_2539_);
v___x_2527_ = v_traceState_2513_;
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
else
{
lean_dec(v_traceState_2513_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2529_);
lean_ctor_set_uint64(v_reuseFailAlloc_2537_, sizeof(void*)*1, v_tid_2525_);
v___x_2531_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2533_; 
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 4, v___x_2531_);
v___x_2533_ = v___x_2523_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_env_2514_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_nextMacroScope_2515_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_ngen_2516_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_auxDeclNGen_2517_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2536_, 5, v_cache_2518_);
lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_messages_2519_);
lean_ctor_set(v_reuseFailAlloc_2536_, 7, v_infoState_2520_);
lean_ctor_set(v_reuseFailAlloc_2536_, 8, v_snapshotTasks_2521_);
v___x_2533_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_st_ref_set(v___y_2507_, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_traces_2511_);
return v___x_2535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2541_);
lean_dec(v___y_2541_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2545_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
uint8_t v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = 0;
v___x_2557_ = lean_box(v___x_2556_);
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
return v_res_2563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2566_ = l_Lean_stringToMessageData(v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2567_, lean_object* v_x_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2572_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2573_ = l_Lean_MessageData_ofName(v_name_2567_);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2576_, lean_object* v_x_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2576_, v_x_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec_ref(v_x_2577_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_x_2582_){
_start:
{
if (lean_obj_tag(v_x_2582_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
v_a_2584_ = lean_ctor_get(v_x_2582_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_x_2582_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v_x_2582_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v_x_2582_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
lean_ctor_set_tag(v___x_2586_, 1);
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
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
v_a_2592_ = lean_ctor_get(v_x_2582_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_x_2582_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v_x_2582_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v_x_2582_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set_tag(v___x_2594_, 0);
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object* v_x_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_e_2603_){
_start:
{
if (lean_obj_tag(v_e_2603_) == 0)
{
uint8_t v___x_2604_; 
v___x_2604_ = 2;
return v___x_2604_;
}
else
{
lean_object* v_a_2605_; uint8_t v___x_2606_; 
v_a_2605_ = lean_ctor_get(v_e_2603_, 0);
v___x_2606_ = lean_unbox(v_a_2605_);
if (v___x_2606_ == 0)
{
uint8_t v___x_2607_; 
v___x_2607_ = 1;
return v___x_2607_;
}
else
{
uint8_t v___x_2608_; 
v___x_2608_ = 0;
return v___x_2608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_e_2609_){
_start:
{
uint8_t v_res_2610_; lean_object* v_r_2611_; 
v_res_2610_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_e_2609_);
lean_dec_ref(v_e_2609_);
v_r_2611_ = lean_box(v_res_2610_);
return v_r_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(size_t v_sz_2612_, size_t v_i_2613_, lean_object* v_bs_2614_){
_start:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_usize_dec_lt(v_i_2613_, v_sz_2612_);
if (v___x_2615_ == 0)
{
return v_bs_2614_;
}
else
{
lean_object* v_v_2616_; lean_object* v_msg_2617_; lean_object* v___x_2618_; lean_object* v_bs_x27_2619_; size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v_v_2616_ = lean_array_uget_borrowed(v_bs_2614_, v_i_2613_);
v_msg_2617_ = lean_ctor_get(v_v_2616_, 1);
lean_inc_ref(v_msg_2617_);
v___x_2618_ = lean_unsigned_to_nat(0u);
v_bs_x27_2619_ = lean_array_uset(v_bs_2614_, v_i_2613_, v___x_2618_);
v___x_2620_ = ((size_t)1ULL);
v___x_2621_ = lean_usize_add(v_i_2613_, v___x_2620_);
v___x_2622_ = lean_array_uset(v_bs_x27_2619_, v_i_2613_, v_msg_2617_);
v_i_2613_ = v___x_2621_;
v_bs_2614_ = v___x_2622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_sz_2624_, lean_object* v_i_2625_, lean_object* v_bs_2626_){
_start:
{
size_t v_sz_boxed_2627_; size_t v_i_boxed_2628_; lean_object* v_res_2629_; 
v_sz_boxed_2627_ = lean_unbox_usize(v_sz_2624_);
lean_dec(v_sz_2624_);
v_i_boxed_2628_ = lean_unbox_usize(v_i_2625_);
lean_dec(v_i_2625_);
v_res_2629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_boxed_2627_, v_i_boxed_2628_, v_bs_2626_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_oldTraces_2630_, lean_object* v_data_2631_, lean_object* v_ref_2632_, lean_object* v_msg_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_fileName_2637_; lean_object* v_fileMap_2638_; lean_object* v_options_2639_; lean_object* v_currRecDepth_2640_; lean_object* v_maxRecDepth_2641_; lean_object* v_ref_2642_; lean_object* v_currNamespace_2643_; lean_object* v_openDecls_2644_; lean_object* v_initHeartbeats_2645_; lean_object* v_maxHeartbeats_2646_; lean_object* v_quotContext_2647_; lean_object* v_currMacroScope_2648_; uint8_t v_diag_2649_; lean_object* v_cancelTk_x3f_2650_; uint8_t v_suppressElabErrors_2651_; lean_object* v_inheritedTraceOptions_2652_; lean_object* v___x_2653_; lean_object* v_traceState_2654_; lean_object* v_traces_2655_; lean_object* v_ref_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; size_t v_sz_2659_; size_t v___x_2660_; lean_object* v___x_2661_; lean_object* v_msg_2662_; lean_object* v___x_2663_; lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2701_; 
v_fileName_2637_ = lean_ctor_get(v___y_2634_, 0);
v_fileMap_2638_ = lean_ctor_get(v___y_2634_, 1);
v_options_2639_ = lean_ctor_get(v___y_2634_, 2);
v_currRecDepth_2640_ = lean_ctor_get(v___y_2634_, 3);
v_maxRecDepth_2641_ = lean_ctor_get(v___y_2634_, 4);
v_ref_2642_ = lean_ctor_get(v___y_2634_, 5);
v_currNamespace_2643_ = lean_ctor_get(v___y_2634_, 6);
v_openDecls_2644_ = lean_ctor_get(v___y_2634_, 7);
v_initHeartbeats_2645_ = lean_ctor_get(v___y_2634_, 8);
v_maxHeartbeats_2646_ = lean_ctor_get(v___y_2634_, 9);
v_quotContext_2647_ = lean_ctor_get(v___y_2634_, 10);
v_currMacroScope_2648_ = lean_ctor_get(v___y_2634_, 11);
v_diag_2649_ = lean_ctor_get_uint8(v___y_2634_, sizeof(void*)*14);
v_cancelTk_x3f_2650_ = lean_ctor_get(v___y_2634_, 12);
v_suppressElabErrors_2651_ = lean_ctor_get_uint8(v___y_2634_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2652_ = lean_ctor_get(v___y_2634_, 13);
v___x_2653_ = lean_st_ref_get(v___y_2635_);
v_traceState_2654_ = lean_ctor_get(v___x_2653_, 4);
lean_inc_ref(v_traceState_2654_);
lean_dec(v___x_2653_);
v_traces_2655_ = lean_ctor_get(v_traceState_2654_, 0);
lean_inc_ref(v_traces_2655_);
lean_dec_ref(v_traceState_2654_);
v_ref_2656_ = l_Lean_replaceRef(v_ref_2632_, v_ref_2642_);
lean_inc_ref(v_inheritedTraceOptions_2652_);
lean_inc(v_cancelTk_x3f_2650_);
lean_inc(v_currMacroScope_2648_);
lean_inc(v_quotContext_2647_);
lean_inc(v_maxHeartbeats_2646_);
lean_inc(v_initHeartbeats_2645_);
lean_inc(v_openDecls_2644_);
lean_inc(v_currNamespace_2643_);
lean_inc(v_maxRecDepth_2641_);
lean_inc(v_currRecDepth_2640_);
lean_inc_ref(v_options_2639_);
lean_inc_ref(v_fileMap_2638_);
lean_inc_ref(v_fileName_2637_);
v___x_2657_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2657_, 0, v_fileName_2637_);
lean_ctor_set(v___x_2657_, 1, v_fileMap_2638_);
lean_ctor_set(v___x_2657_, 2, v_options_2639_);
lean_ctor_set(v___x_2657_, 3, v_currRecDepth_2640_);
lean_ctor_set(v___x_2657_, 4, v_maxRecDepth_2641_);
lean_ctor_set(v___x_2657_, 5, v_ref_2656_);
lean_ctor_set(v___x_2657_, 6, v_currNamespace_2643_);
lean_ctor_set(v___x_2657_, 7, v_openDecls_2644_);
lean_ctor_set(v___x_2657_, 8, v_initHeartbeats_2645_);
lean_ctor_set(v___x_2657_, 9, v_maxHeartbeats_2646_);
lean_ctor_set(v___x_2657_, 10, v_quotContext_2647_);
lean_ctor_set(v___x_2657_, 11, v_currMacroScope_2648_);
lean_ctor_set(v___x_2657_, 12, v_cancelTk_x3f_2650_);
lean_ctor_set(v___x_2657_, 13, v_inheritedTraceOptions_2652_);
lean_ctor_set_uint8(v___x_2657_, sizeof(void*)*14, v_diag_2649_);
lean_ctor_set_uint8(v___x_2657_, sizeof(void*)*14 + 1, v_suppressElabErrors_2651_);
v___x_2658_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2655_);
lean_dec_ref(v_traces_2655_);
v_sz_2659_ = lean_array_size(v___x_2658_);
v___x_2660_ = ((size_t)0ULL);
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_2659_, v___x_2660_, v___x_2658_);
v_msg_2662_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2662_, 0, v_data_2631_);
lean_ctor_set(v_msg_2662_, 1, v_msg_2633_);
lean_ctor_set(v_msg_2662_, 2, v___x_2661_);
v___x_2663_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2662_, v___x_2657_, v___y_2635_);
lean_dec_ref(v___x_2657_);
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2701_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2701_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v_traceState_2669_; lean_object* v_env_2670_; lean_object* v_nextMacroScope_2671_; lean_object* v_ngen_2672_; lean_object* v_auxDeclNGen_2673_; lean_object* v_cache_2674_; lean_object* v_messages_2675_; lean_object* v_infoState_2676_; lean_object* v_snapshotTasks_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2700_; 
v___x_2668_ = lean_st_ref_take(v___y_2635_);
v_traceState_2669_ = lean_ctor_get(v___x_2668_, 4);
v_env_2670_ = lean_ctor_get(v___x_2668_, 0);
v_nextMacroScope_2671_ = lean_ctor_get(v___x_2668_, 1);
v_ngen_2672_ = lean_ctor_get(v___x_2668_, 2);
v_auxDeclNGen_2673_ = lean_ctor_get(v___x_2668_, 3);
v_cache_2674_ = lean_ctor_get(v___x_2668_, 5);
v_messages_2675_ = lean_ctor_get(v___x_2668_, 6);
v_infoState_2676_ = lean_ctor_get(v___x_2668_, 7);
v_snapshotTasks_2677_ = lean_ctor_get(v___x_2668_, 8);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2679_ = v___x_2668_;
v_isShared_2680_ = v_isSharedCheck_2700_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_snapshotTasks_2677_);
lean_inc(v_infoState_2676_);
lean_inc(v_messages_2675_);
lean_inc(v_cache_2674_);
lean_inc(v_traceState_2669_);
lean_inc(v_auxDeclNGen_2673_);
lean_inc(v_ngen_2672_);
lean_inc(v_nextMacroScope_2671_);
lean_inc(v_env_2670_);
lean_dec(v___x_2668_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2700_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
uint64_t v_tid_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2698_; 
v_tid_2681_ = lean_ctor_get_uint64(v_traceState_2669_, sizeof(void*)*1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_traceState_2669_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v_traceState_2669_, 0);
lean_dec(v_unused_2699_);
v___x_2683_ = v_traceState_2669_;
v_isShared_2684_ = v_isSharedCheck_2698_;
goto v_resetjp_2682_;
}
else
{
lean_dec(v_traceState_2669_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2698_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v_ref_2632_);
lean_ctor_set(v___x_2685_, 1, v_a_2664_);
v___x_2686_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2630_, v___x_2685_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2686_);
v___x_2688_ = v___x_2683_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2686_);
lean_ctor_set_uint64(v_reuseFailAlloc_2697_, sizeof(void*)*1, v_tid_2681_);
v___x_2688_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2690_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 4, v___x_2688_);
v___x_2690_ = v___x_2679_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_env_2670_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_nextMacroScope_2671_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_ngen_2672_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_auxDeclNGen_2673_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2696_, 5, v_cache_2674_);
lean_ctor_set(v_reuseFailAlloc_2696_, 6, v_messages_2675_);
lean_ctor_set(v_reuseFailAlloc_2696_, 7, v_infoState_2676_);
lean_ctor_set(v_reuseFailAlloc_2696_, 8, v_snapshotTasks_2677_);
v___x_2690_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2691_ = lean_st_ref_set(v___y_2635_, v___x_2690_);
v___x_2692_ = lean_box(0);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2692_);
v___x_2694_ = v___x_2666_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_oldTraces_2702_, lean_object* v_data_2703_, lean_object* v_ref_2704_, lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2702_, v_data_2703_, v_ref_2704_, v_msg_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2709_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2712_ = l_Lean_stringToMessageData(v___x_2711_);
return v___x_2712_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2));
v___x_2715_ = l_Lean_stringToMessageData(v___x_2714_);
return v___x_2715_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4(void){
_start:
{
lean_object* v___x_2716_; double v___x_2717_; 
v___x_2716_ = lean_unsigned_to_nat(1000u);
v___x_2717_ = lean_float_of_nat(v___x_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2718_, uint8_t v_collapsed_2719_, lean_object* v_tag_2720_, lean_object* v_opts_2721_, uint8_t v_clsEnabled_2722_, lean_object* v_oldTraces_2723_, lean_object* v_msg_2724_, lean_object* v_resStartStop_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_fst_2729_; lean_object* v_snd_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2828_; 
v_fst_2729_ = lean_ctor_get(v_resStartStop_2725_, 0);
v_snd_2730_ = lean_ctor_get(v_resStartStop_2725_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_resStartStop_2725_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2732_ = v_resStartStop_2725_;
v_isShared_2733_ = v_isSharedCheck_2828_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_snd_2730_);
lean_inc(v_fst_2729_);
lean_dec(v_resStartStop_2725_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2828_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v_data_2737_; lean_object* v_fst_2748_; lean_object* v_snd_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2827_; 
v_fst_2748_ = lean_ctor_get(v_snd_2730_, 0);
v_snd_2749_ = lean_ctor_get(v_snd_2730_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_snd_2730_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2751_ = v_snd_2730_;
v_isShared_2752_ = v_isSharedCheck_2827_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_snd_2749_);
lean_inc(v_fst_2748_);
lean_dec(v_snd_2730_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2827_;
goto v_resetjp_2750_;
}
v___jp_2734_:
{
lean_object* v___x_2738_; 
lean_inc(v___y_2736_);
v___x_2738_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2723_, v_data_2737_, v___y_2736_, v___y_2735_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v___x_2739_; 
lean_dec_ref(v___x_2738_);
v___x_2739_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2729_);
return v___x_2739_;
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_fst_2729_);
v_a_2740_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2738_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2738_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; uint8_t v___x_2754_; lean_object* v___y_2756_; lean_object* v_a_2757_; uint8_t v___y_2781_; double v___y_2812_; 
v___x_2753_ = l_Lean_trace_profiler;
v___x_2754_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2721_, v___x_2753_);
if (v___x_2754_ == 0)
{
v___y_2781_ = v___x_2754_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2818_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2721_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; double v___x_2821_; double v___x_2822_; double v___x_2823_; 
v___x_2819_ = l_Lean_trace_profiler_threshold;
v___x_2820_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2721_, v___x_2819_);
v___x_2821_ = lean_float_of_nat(v___x_2820_);
v___x_2822_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4);
v___x_2823_ = lean_float_div(v___x_2821_, v___x_2822_);
v___y_2812_ = v___x_2823_;
goto v___jp_2811_;
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; double v___x_2826_; 
v___x_2824_ = l_Lean_trace_profiler_threshold;
v___x_2825_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2721_, v___x_2824_);
v___x_2826_ = lean_float_of_nat(v___x_2825_);
v___y_2812_ = v___x_2826_;
goto v___jp_2811_;
}
}
v___jp_2755_:
{
uint8_t v_result_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v_result_2758_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_fst_2729_);
v___x_2759_ = l_Lean_TraceResult_toEmoji(v_result_2758_);
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
v___x_2761_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
if (v_isShared_2752_ == 0)
{
lean_ctor_set_tag(v___x_2751_, 7);
lean_ctor_set(v___x_2751_, 1, v___x_2761_);
lean_ctor_set(v___x_2751_, 0, v___x_2760_);
v___x_2763_ = v___x_2751_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v_m_2765_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 7);
lean_ctor_set(v___x_2732_, 1, v_a_2757_);
lean_ctor_set(v___x_2732_, 0, v___x_2763_);
v_m_2765_ = v___x_2732_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2763_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_a_2757_);
v_m_2765_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; double v___x_2768_; lean_object* v_data_2769_; 
v___x_2766_ = lean_box(v_result_2758_);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v___x_2768_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0);
lean_inc_ref(v_tag_2720_);
lean_inc_ref(v___x_2767_);
lean_inc(v_cls_2718_);
v_data_2769_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2769_, 0, v_cls_2718_);
lean_ctor_set(v_data_2769_, 1, v___x_2767_);
lean_ctor_set(v_data_2769_, 2, v_tag_2720_);
lean_ctor_set_float(v_data_2769_, sizeof(void*)*3, v___x_2768_);
lean_ctor_set_float(v_data_2769_, sizeof(void*)*3 + 8, v___x_2768_);
lean_ctor_set_uint8(v_data_2769_, sizeof(void*)*3 + 16, v_collapsed_2719_);
if (v___x_2754_ == 0)
{
lean_dec_ref(v___x_2767_);
lean_dec(v_snd_2749_);
lean_dec(v_fst_2748_);
lean_dec_ref(v_tag_2720_);
lean_dec(v_cls_2718_);
v___y_2735_ = v_m_2765_;
v___y_2736_ = v___y_2756_;
v_data_2737_ = v_data_2769_;
goto v___jp_2734_;
}
else
{
lean_object* v_data_2770_; double v___x_2771_; double v___x_2772_; 
lean_dec_ref(v_data_2769_);
v_data_2770_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2770_, 0, v_cls_2718_);
lean_ctor_set(v_data_2770_, 1, v___x_2767_);
lean_ctor_set(v_data_2770_, 2, v_tag_2720_);
v___x_2771_ = lean_unbox_float(v_fst_2748_);
lean_dec(v_fst_2748_);
lean_ctor_set_float(v_data_2770_, sizeof(void*)*3, v___x_2771_);
v___x_2772_ = lean_unbox_float(v_snd_2749_);
lean_dec(v_snd_2749_);
lean_ctor_set_float(v_data_2770_, sizeof(void*)*3 + 8, v___x_2772_);
lean_ctor_set_uint8(v_data_2770_, sizeof(void*)*3 + 16, v_collapsed_2719_);
v___y_2735_ = v_m_2765_;
v___y_2736_ = v___y_2756_;
v_data_2737_ = v_data_2770_;
goto v___jp_2734_;
}
}
}
}
v___jp_2775_:
{
lean_object* v_ref_2776_; lean_object* v___x_2777_; 
v_ref_2776_ = lean_ctor_get(v___y_2726_, 5);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v_fst_2729_);
v___x_2777_ = lean_apply_4(v_msg_2724_, v_fst_2729_, v___y_2726_, v___y_2727_, lean_box(0));
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref(v___x_2777_);
v___y_2756_ = v_ref_2776_;
v_a_2757_ = v_a_2778_;
goto v___jp_2755_;
}
else
{
lean_object* v___x_2779_; 
lean_dec_ref(v___x_2777_);
v___x_2779_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3);
v___y_2756_ = v_ref_2776_;
v_a_2757_ = v___x_2779_;
goto v___jp_2755_;
}
}
v___jp_2780_:
{
if (v_clsEnabled_2722_ == 0)
{
if (v___y_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v_traceState_2783_; lean_object* v_env_2784_; lean_object* v_nextMacroScope_2785_; lean_object* v_ngen_2786_; lean_object* v_auxDeclNGen_2787_; lean_object* v_cache_2788_; lean_object* v_messages_2789_; lean_object* v_infoState_2790_; lean_object* v_snapshotTasks_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2810_; 
lean_del_object(v___x_2751_);
lean_dec(v_snd_2749_);
lean_dec(v_fst_2748_);
lean_del_object(v___x_2732_);
lean_dec_ref(v_msg_2724_);
lean_dec_ref(v_tag_2720_);
lean_dec(v_cls_2718_);
v___x_2782_ = lean_st_ref_take(v___y_2727_);
v_traceState_2783_ = lean_ctor_get(v___x_2782_, 4);
v_env_2784_ = lean_ctor_get(v___x_2782_, 0);
v_nextMacroScope_2785_ = lean_ctor_get(v___x_2782_, 1);
v_ngen_2786_ = lean_ctor_get(v___x_2782_, 2);
v_auxDeclNGen_2787_ = lean_ctor_get(v___x_2782_, 3);
v_cache_2788_ = lean_ctor_get(v___x_2782_, 5);
v_messages_2789_ = lean_ctor_get(v___x_2782_, 6);
v_infoState_2790_ = lean_ctor_get(v___x_2782_, 7);
v_snapshotTasks_2791_ = lean_ctor_get(v___x_2782_, 8);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2793_ = v___x_2782_;
v_isShared_2794_ = v_isSharedCheck_2810_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_snapshotTasks_2791_);
lean_inc(v_infoState_2790_);
lean_inc(v_messages_2789_);
lean_inc(v_cache_2788_);
lean_inc(v_traceState_2783_);
lean_inc(v_auxDeclNGen_2787_);
lean_inc(v_ngen_2786_);
lean_inc(v_nextMacroScope_2785_);
lean_inc(v_env_2784_);
lean_dec(v___x_2782_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2810_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
uint64_t v_tid_2795_; lean_object* v_traces_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2809_; 
v_tid_2795_ = lean_ctor_get_uint64(v_traceState_2783_, sizeof(void*)*1);
v_traces_2796_ = lean_ctor_get(v_traceState_2783_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_traceState_2783_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2798_ = v_traceState_2783_;
v_isShared_2799_ = v_isSharedCheck_2809_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_traces_2796_);
lean_dec(v_traceState_2783_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2809_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2800_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2723_, v_traces_2796_);
lean_dec_ref(v_traces_2796_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2800_);
v___x_2802_ = v___x_2798_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2800_);
lean_ctor_set_uint64(v_reuseFailAlloc_2808_, sizeof(void*)*1, v_tid_2795_);
v___x_2802_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 4, v___x_2802_);
v___x_2804_ = v___x_2793_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_env_2784_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_nextMacroScope_2785_);
lean_ctor_set(v_reuseFailAlloc_2807_, 2, v_ngen_2786_);
lean_ctor_set(v_reuseFailAlloc_2807_, 3, v_auxDeclNGen_2787_);
lean_ctor_set(v_reuseFailAlloc_2807_, 4, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2807_, 5, v_cache_2788_);
lean_ctor_set(v_reuseFailAlloc_2807_, 6, v_messages_2789_);
lean_ctor_set(v_reuseFailAlloc_2807_, 7, v_infoState_2790_);
lean_ctor_set(v_reuseFailAlloc_2807_, 8, v_snapshotTasks_2791_);
v___x_2804_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_st_ref_set(v___y_2727_, v___x_2804_);
v___x_2806_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2729_);
return v___x_2806_;
}
}
}
}
}
else
{
goto v___jp_2775_;
}
}
else
{
goto v___jp_2775_;
}
}
v___jp_2811_:
{
double v___x_2813_; double v___x_2814_; double v___x_2815_; uint8_t v___x_2816_; 
v___x_2813_ = lean_unbox_float(v_snd_2749_);
v___x_2814_ = lean_unbox_float(v_fst_2748_);
v___x_2815_ = lean_float_sub(v___x_2813_, v___x_2814_);
v___x_2816_ = lean_float_decLt(v___y_2812_, v___x_2815_);
v___y_2781_ = v___x_2816_;
goto v___jp_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_2829_, lean_object* v_collapsed_2830_, lean_object* v_tag_2831_, lean_object* v_opts_2832_, lean_object* v_clsEnabled_2833_, lean_object* v_oldTraces_2834_, lean_object* v_msg_2835_, lean_object* v_resStartStop_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
uint8_t v_collapsed_boxed_2840_; uint8_t v_clsEnabled_boxed_2841_; lean_object* v_res_2842_; 
v_collapsed_boxed_2840_ = lean_unbox(v_collapsed_2830_);
v_clsEnabled_boxed_2841_ = lean_unbox(v_clsEnabled_2833_);
v_res_2842_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_2829_, v_collapsed_boxed_2840_, v_tag_2831_, v_opts_2832_, v_clsEnabled_boxed_2841_, v_oldTraces_2834_, v_msg_2835_, v_resStartStop_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec_ref(v_opts_2832_);
return v_res_2842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2846_ = lean_unsigned_to_nat(0u);
v___x_2847_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
lean_ctor_set(v___x_2847_, 2, v___x_2846_);
lean_ctor_set(v___x_2847_, 3, v___x_2846_);
lean_ctor_set(v___x_2847_, 4, v___x_2845_);
lean_ctor_set(v___x_2847_, 5, v___x_2845_);
lean_ctor_set(v___x_2847_, 6, v___x_2845_);
lean_ctor_set(v___x_2847_, 7, v___x_2845_);
lean_ctor_set(v___x_2847_, 8, v___x_2845_);
lean_ctor_set(v___x_2847_, 9, v___x_2845_);
return v___x_2847_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2849_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
lean_ctor_set(v___x_2849_, 2, v___x_2848_);
lean_ctor_set(v___x_2849_, 3, v___x_2848_);
lean_ctor_set(v___x_2849_, 4, v___x_2848_);
lean_ctor_set(v___x_2849_, 5, v___x_2848_);
return v___x_2849_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
lean_ctor_set(v___x_2851_, 2, v___x_2850_);
lean_ctor_set(v___x_2851_, 3, v___x_2850_);
lean_ctor_set(v___x_2851_, 4, v___x_2850_);
return v___x_2851_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2852_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2853_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_2854_ = lean_box(1);
v___x_2855_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2856_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2855_);
lean_ctor_set(v___x_2857_, 2, v___x_2854_);
lean_ctor_set(v___x_2857_, 3, v___x_2853_);
lean_ctor_set(v___x_2857_, 4, v___x_2852_);
return v___x_2857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2862_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_2863_ = l_Lean_Name_append(v___x_2862_, v___x_2861_);
return v___x_2863_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2864_; double v___x_2865_; 
v___x_2864_ = lean_unsigned_to_nat(1000000000u);
v___x_2865_ = lean_float_of_nat(v___x_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_2866_, lean_object* v_name_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_options_2871_; uint8_t v_hasTrace_2872_; 
v_options_2871_ = lean_ctor_get(v___y_2868_, 2);
v_hasTrace_2872_ = lean_ctor_get_uint8(v_options_2871_, sizeof(void*)*1);
if (v_hasTrace_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v_env_2874_; lean_object* v___x_2875_; 
lean_dec_ref(v___f_2866_);
v___x_2873_ = lean_st_ref_get(v___y_2869_);
v_env_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc_ref(v_env_2874_);
lean_dec(v___x_2873_);
lean_inc(v_name_2867_);
v___x_2875_ = l_Lean_Meta_declFromEqLikeName(v_env_2874_, v_name_2867_);
if (lean_obj_tag(v___x_2875_) == 1)
{
lean_object* v_val_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2975_; 
v_val_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2975_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_val_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2975_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_fst_2880_; lean_object* v_snd_2881_; lean_object* v___x_2882_; lean_object* v_env_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_fst_2880_ = lean_ctor_get(v_val_2876_, 0);
lean_inc_n(v_fst_2880_, 2);
v_snd_2881_ = lean_ctor_get(v_val_2876_, 1);
lean_inc_n(v_snd_2881_, 2);
lean_dec(v_val_2876_);
v___x_2882_ = lean_st_ref_get(v___y_2869_);
v_env_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc_ref(v_env_2883_);
lean_dec(v___x_2882_);
v___x_2884_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2883_, v_fst_2880_, v_snd_2881_);
v___x_2885_ = lean_name_eq(v_name_2867_, v___x_2884_);
lean_dec(v___x_2884_);
lean_dec(v_name_2867_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_dec(v_snd_2881_);
lean_dec(v_fst_2880_);
v___x_2886_ = lean_box(v_hasTrace_2872_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2886_);
v___x_2888_ = v___x_2878_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
else
{
uint8_t v___x_2890_; lean_object* v_a_2892_; 
lean_inc(v_snd_2881_);
v___x_2890_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_2881_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2906_; uint8_t v___x_2907_; lean_object* v_a_2909_; 
lean_del_object(v___x_2878_);
v___x_2906_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_2907_ = lean_string_dec_eq(v_snd_2881_, v___x_2906_);
lean_dec(v_snd_2881_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v_fst_2880_);
v___x_2921_ = lean_box(v_hasTrace_2872_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
else
{
uint8_t v___x_2923_; uint8_t v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; uint64_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2923_ = 1;
v___x_2924_ = 0;
v___x_2925_ = 2;
v___x_2926_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2926_, 0, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2926_, 1, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2926_, 2, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2926_, 3, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2926_, 4, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2926_, 5, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 6, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 7, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2926_, 8, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 9, v___x_2923_);
lean_ctor_set_uint8(v___x_2926_, 10, v___x_2924_);
lean_ctor_set_uint8(v___x_2926_, 11, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 12, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 13, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 14, v___x_2925_);
lean_ctor_set_uint8(v___x_2926_, 15, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 16, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 17, v___x_2907_);
lean_ctor_set_uint8(v___x_2926_, 18, v___x_2907_);
v___x_2927_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set_uint64(v___x_2928_, sizeof(void*)*1, v___x_2927_);
v___x_2929_ = lean_box(1);
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2932_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2934_, 0, v___x_2928_);
lean_ctor_set(v___x_2934_, 1, v___x_2929_);
lean_ctor_set(v___x_2934_, 2, v___x_2931_);
lean_ctor_set(v___x_2934_, 3, v___x_2932_);
lean_ctor_set(v___x_2934_, 4, v___x_2933_);
lean_ctor_set(v___x_2934_, 5, v___x_2930_);
lean_ctor_set(v___x_2934_, 6, v___x_2933_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*7, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*7 + 1, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*7 + 2, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*7 + 3, v___x_2885_);
v___x_2935_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2936_ = lean_st_mk_ref(v___x_2935_);
v___x_2937_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_2880_, v___x_2885_, v___x_2934_, v___x_2936_, v___y_2868_, v___y_2869_);
lean_dec_ref(v___x_2934_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref(v___x_2937_);
v___x_2939_ = lean_st_ref_get(v___x_2936_);
lean_dec(v___x_2936_);
lean_dec(v___x_2939_);
v_a_2909_ = v_a_2938_;
goto v___jp_2908_;
}
else
{
lean_dec(v___x_2936_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2940_; 
v_a_2940_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2940_);
lean_dec_ref(v___x_2937_);
v_a_2909_ = v_a_2940_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_a_2941_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2937_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2937_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
v___jp_2908_:
{
if (lean_obj_tag(v_a_2909_) == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_box(v_hasTrace_2872_);
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
else
{
lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
v_isSharedCheck_2919_ = !lean_is_exclusive(v_a_2909_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v_a_2909_, 0);
lean_dec(v_unused_2920_);
v___x_2913_ = v_a_2909_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_dec(v_a_2909_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = lean_box(v___x_2907_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set_tag(v___x_2913_, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
else
{
uint8_t v___x_2949_; uint8_t v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; uint64_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
lean_dec(v_snd_2881_);
v___x_2949_ = 1;
v___x_2950_ = 0;
v___x_2951_ = 2;
v___x_2952_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2952_, 0, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2952_, 1, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2952_, 2, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2952_, 3, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2952_, 4, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2952_, 5, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 6, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 7, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2952_, 8, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 9, v___x_2949_);
lean_ctor_set_uint8(v___x_2952_, 10, v___x_2950_);
lean_ctor_set_uint8(v___x_2952_, 11, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 12, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 13, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 14, v___x_2951_);
lean_ctor_set_uint8(v___x_2952_, 15, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 16, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 17, v___x_2890_);
lean_ctor_set_uint8(v___x_2952_, 18, v___x_2890_);
v___x_2953_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set_uint64(v___x_2954_, sizeof(void*)*1, v___x_2953_);
v___x_2955_ = lean_box(1);
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2958_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2960_, 0, v___x_2954_);
lean_ctor_set(v___x_2960_, 1, v___x_2955_);
lean_ctor_set(v___x_2960_, 2, v___x_2957_);
lean_ctor_set(v___x_2960_, 3, v___x_2958_);
lean_ctor_set(v___x_2960_, 4, v___x_2959_);
lean_ctor_set(v___x_2960_, 5, v___x_2956_);
lean_ctor_set(v___x_2960_, 6, v___x_2959_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*7, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*7 + 1, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*7 + 2, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*7 + 3, v___x_2885_);
v___x_2961_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2962_ = lean_st_mk_ref(v___x_2961_);
v___x_2963_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_2880_, v___x_2960_, v___x_2962_, v___y_2868_, v___y_2869_);
lean_dec_ref(v___x_2960_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = lean_st_ref_get(v___x_2962_);
lean_dec(v___x_2962_);
lean_dec(v___x_2965_);
v_a_2892_ = v_a_2964_;
goto v___jp_2891_;
}
else
{
lean_dec(v___x_2962_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2966_; 
v_a_2966_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2963_);
v_a_2892_ = v_a_2966_;
goto v___jp_2891_;
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_del_object(v___x_2878_);
v_a_2967_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2963_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2963_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
v___jp_2891_:
{
if (lean_obj_tag(v_a_2892_) == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = lean_box(v_hasTrace_2872_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2893_);
v___x_2895_ = v___x_2878_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
else
{
lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2904_; 
lean_del_object(v___x_2878_);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_a_2892_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v_a_2892_, 0);
lean_dec(v_unused_2905_);
v___x_2898_ = v_a_2892_;
v_isShared_2899_ = v_isSharedCheck_2904_;
goto v_resetjp_2897_;
}
else
{
lean_dec(v_a_2892_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2904_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = lean_box(v___x_2890_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set_tag(v___x_2898_, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2900_);
v___x_2902_ = v___x_2898_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_dec(v___x_2875_);
lean_dec(v_name_2867_);
v___x_2976_ = lean_box(v_hasTrace_2872_);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v_a_2987_; lean_object* v___y_3000_; lean_object* v___y_3001_; uint8_t v_a_3002_; uint8_t v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v_a_3009_; uint8_t v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v_a_3014_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v_a_3018_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v_a_3023_; lean_object* v___y_3033_; lean_object* v___y_3034_; uint8_t v_a_3035_; uint8_t v___y_3039_; uint8_t v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v_a_3043_; uint8_t v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v_a_3048_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v_a_3053_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; 
v_inheritedTraceOptions_2978_ = lean_ctor_get(v___y_2868_, 13);
lean_inc(v_name_2867_);
v___f_2979_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_2979_, 0, v_name_2867_);
v___x_2980_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2981_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1));
v___x_2982_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2983_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2978_, v_options_2871_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_3178_; uint8_t v___x_3179_; lean_object* v_a_3181_; lean_object* v_a_3194_; 
v___x_3178_ = l_Lean_trace_profiler;
v___x_3179_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_2871_, v___x_3178_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3206_; lean_object* v_env_3207_; lean_object* v___x_3208_; 
lean_dec_ref(v___f_2979_);
lean_dec_ref(v___f_2866_);
v___x_3206_ = lean_st_ref_get(v___y_2869_);
v_env_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc_ref(v_env_3207_);
lean_dec(v___x_3206_);
lean_inc(v_name_2867_);
v___x_3208_ = l_Lean_Meta_declFromEqLikeName(v_env_3207_, v_name_2867_);
if (lean_obj_tag(v___x_3208_) == 1)
{
lean_object* v_val_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3282_; 
v_val_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3282_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_val_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3282_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_fst_3213_; lean_object* v_snd_3214_; lean_object* v___x_3215_; lean_object* v_env_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; 
v_fst_3213_ = lean_ctor_get(v_val_3209_, 0);
lean_inc_n(v_fst_3213_, 2);
v_snd_3214_ = lean_ctor_get(v_val_3209_, 1);
lean_inc_n(v_snd_3214_, 2);
lean_dec(v_val_3209_);
v___x_3215_ = lean_st_ref_get(v___y_2869_);
v_env_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc_ref(v_env_3216_);
lean_dec(v___x_3215_);
v___x_3217_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3216_, v_fst_3213_, v_snd_3214_);
v___x_3218_ = lean_name_eq(v_name_2867_, v___x_3217_);
lean_dec(v___x_3217_);
lean_dec(v_name_2867_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_dec(v_snd_3214_);
lean_dec(v_fst_3213_);
v___x_3219_ = lean_box(v___x_3179_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3219_);
v___x_3221_ = v___x_3211_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
else
{
uint8_t v___x_3223_; 
lean_inc(v_snd_3214_);
v___x_3223_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3214_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3225_ = lean_string_dec_eq(v_snd_3214_, v___x_3224_);
lean_dec(v_snd_3214_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3228_; 
lean_dec(v_fst_3213_);
v___x_3226_ = lean_box(v___x_3179_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3226_);
v___x_3228_ = v___x_3211_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
else
{
uint8_t v___x_3230_; uint8_t v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; uint64_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_del_object(v___x_3211_);
v___x_3230_ = 1;
v___x_3231_ = 0;
v___x_3232_ = 2;
v___x_3233_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3233_, 0, v___x_3179_);
lean_ctor_set_uint8(v___x_3233_, 1, v___x_3179_);
lean_ctor_set_uint8(v___x_3233_, 2, v___x_3179_);
lean_ctor_set_uint8(v___x_3233_, 3, v___x_3179_);
lean_ctor_set_uint8(v___x_3233_, 4, v___x_3179_);
lean_ctor_set_uint8(v___x_3233_, 5, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 6, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 7, v___x_3179_);
lean_ctor_set_uint8(v___x_3233_, 8, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 9, v___x_3230_);
lean_ctor_set_uint8(v___x_3233_, 10, v___x_3231_);
lean_ctor_set_uint8(v___x_3233_, 11, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 12, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 13, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 14, v___x_3232_);
lean_ctor_set_uint8(v___x_3233_, 15, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 16, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 17, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3233_, 18, v_hasTrace_2872_);
v___x_3234_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3233_);
v___x_3235_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set_uint64(v___x_3235_, sizeof(void*)*1, v___x_3234_);
v___x_3236_ = lean_box(1);
v___x_3237_ = lean_unsigned_to_nat(0u);
v___x_3238_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3239_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3240_ = lean_box(0);
v___x_3241_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3241_, 0, v___x_3235_);
lean_ctor_set(v___x_3241_, 1, v___x_3236_);
lean_ctor_set(v___x_3241_, 2, v___x_3238_);
lean_ctor_set(v___x_3241_, 3, v___x_3239_);
lean_ctor_set(v___x_3241_, 4, v___x_3240_);
lean_ctor_set(v___x_3241_, 5, v___x_3237_);
lean_ctor_set(v___x_3241_, 6, v___x_3240_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*7, v___x_3179_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*7 + 1, v___x_3179_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*7 + 2, v___x_3179_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*7 + 3, v_hasTrace_2872_);
v___x_3242_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3243_ = lean_st_mk_ref(v___x_3242_);
v___x_3244_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3213_, v_hasTrace_2872_, v___x_3241_, v___x_3243_, v___y_2868_, v___y_2869_);
lean_dec_ref(v___x_3241_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref(v___x_3244_);
v___x_3246_ = lean_st_ref_get(v___x_3243_);
lean_dec(v___x_3243_);
lean_dec(v___x_3246_);
v_a_3194_ = v_a_3245_;
goto v___jp_3193_;
}
else
{
lean_dec(v___x_3243_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3247_; 
v_a_3247_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3247_);
lean_dec_ref(v___x_3244_);
v_a_3194_ = v_a_3247_;
goto v___jp_3193_;
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
v_a_3248_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3244_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3244_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
}
else
{
uint8_t v___x_3256_; uint8_t v___x_3257_; uint8_t v___x_3258_; lean_object* v___x_3259_; uint64_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec(v_snd_3214_);
lean_del_object(v___x_3211_);
v___x_3256_ = 1;
v___x_3257_ = 0;
v___x_3258_ = 2;
v___x_3259_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3259_, 0, v___x_3179_);
lean_ctor_set_uint8(v___x_3259_, 1, v___x_3179_);
lean_ctor_set_uint8(v___x_3259_, 2, v___x_3179_);
lean_ctor_set_uint8(v___x_3259_, 3, v___x_3179_);
lean_ctor_set_uint8(v___x_3259_, 4, v___x_3179_);
lean_ctor_set_uint8(v___x_3259_, 5, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 6, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 7, v___x_3179_);
lean_ctor_set_uint8(v___x_3259_, 8, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 9, v___x_3256_);
lean_ctor_set_uint8(v___x_3259_, 10, v___x_3257_);
lean_ctor_set_uint8(v___x_3259_, 11, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 12, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 13, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 14, v___x_3258_);
lean_ctor_set_uint8(v___x_3259_, 15, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 16, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 17, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3259_, 18, v_hasTrace_2872_);
v___x_3260_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3259_);
v___x_3261_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3261_, 0, v___x_3259_);
lean_ctor_set_uint64(v___x_3261_, sizeof(void*)*1, v___x_3260_);
v___x_3262_ = lean_box(1);
v___x_3263_ = lean_unsigned_to_nat(0u);
v___x_3264_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3265_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3266_ = lean_box(0);
v___x_3267_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3267_, 0, v___x_3261_);
lean_ctor_set(v___x_3267_, 1, v___x_3262_);
lean_ctor_set(v___x_3267_, 2, v___x_3264_);
lean_ctor_set(v___x_3267_, 3, v___x_3265_);
lean_ctor_set(v___x_3267_, 4, v___x_3266_);
lean_ctor_set(v___x_3267_, 5, v___x_3263_);
lean_ctor_set(v___x_3267_, 6, v___x_3266_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*7, v___x_3179_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*7 + 1, v___x_3179_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*7 + 2, v___x_3179_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*7 + 3, v_hasTrace_2872_);
v___x_3268_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3269_ = lean_st_mk_ref(v___x_3268_);
v___x_3270_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3213_, v___x_3267_, v___x_3269_, v___y_2868_, v___y_2869_);
lean_dec_ref(v___x_3267_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref(v___x_3270_);
v___x_3272_ = lean_st_ref_get(v___x_3269_);
lean_dec(v___x_3269_);
lean_dec(v___x_3272_);
v_a_3181_ = v_a_3271_;
goto v___jp_3180_;
}
else
{
lean_dec(v___x_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3273_; 
v_a_3273_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3273_);
lean_dec_ref(v___x_3270_);
v_a_3181_ = v_a_3273_;
goto v___jp_3180_;
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
v_a_3274_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3270_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3270_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
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
lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec(v___x_3208_);
lean_dec(v_name_2867_);
v___x_3283_ = lean_box(v___x_3179_);
v___x_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
return v___x_3284_;
}
}
else
{
goto v___jp_3062_;
}
v___jp_3180_:
{
if (lean_obj_tag(v_a_3181_) == 0)
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(v___x_3179_);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
else
{
lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3191_; 
v_isSharedCheck_3191_ = !lean_is_exclusive(v_a_3181_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v_a_3181_, 0);
lean_dec(v_unused_3192_);
v___x_3185_ = v_a_3181_;
v_isShared_3186_ = v_isSharedCheck_3191_;
goto v_resetjp_3184_;
}
else
{
lean_dec(v_a_3181_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3191_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = lean_box(v_hasTrace_2872_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
v___jp_3193_:
{
if (lean_obj_tag(v_a_3194_) == 0)
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_box(v___x_3179_);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
return v___x_3196_;
}
else
{
lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3204_; 
v_isSharedCheck_3204_ = !lean_is_exclusive(v_a_3194_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; 
v_unused_3205_ = lean_ctor_get(v_a_3194_, 0);
lean_dec(v_unused_3205_);
v___x_3198_ = v_a_3194_;
v_isShared_3199_ = v_isSharedCheck_3204_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v_a_3194_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3204_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3200_ = lean_box(v_hasTrace_2872_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set_tag(v___x_3198_, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3200_);
v___x_3202_ = v___x_3198_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
else
{
goto v___jp_3062_;
}
v___jp_2984_:
{
lean_object* v___x_2988_; double v___x_2989_; double v___x_2990_; double v___x_2991_; double v___x_2992_; double v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2988_ = lean_io_mono_nanos_now();
v___x_2989_ = lean_float_of_nat(v___y_2985_);
v___x_2990_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2991_ = lean_float_div(v___x_2989_, v___x_2990_);
v___x_2992_ = lean_float_of_nat(v___x_2988_);
v___x_2993_ = lean_float_div(v___x_2992_, v___x_2990_);
v___x_2994_ = lean_box_float(v___x_2991_);
v___x_2995_ = lean_box_float(v___x_2993_);
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2994_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_a_2987_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_2980_, v_hasTrace_2872_, v___x_2981_, v_options_2871_, v___x_2983_, v___y_2986_, v___f_2979_, v___x_2997_, v___y_2868_, v___y_2869_);
return v___x_2998_;
}
v___jp_2999_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_box(v_a_3002_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
v___y_2985_ = v___y_3000_;
v___y_2986_ = v___y_3001_;
v_a_2987_ = v___x_3004_;
goto v___jp_2984_;
}
v___jp_3005_:
{
if (lean_obj_tag(v_a_3009_) == 0)
{
v___y_3000_ = v___y_3007_;
v___y_3001_ = v___y_3008_;
v_a_3002_ = v___y_3006_;
goto v___jp_2999_;
}
else
{
lean_dec_ref(v_a_3009_);
v___y_3000_ = v___y_3007_;
v___y_3001_ = v___y_3008_;
v_a_3002_ = v_hasTrace_2872_;
goto v___jp_2999_;
}
}
v___jp_3010_:
{
if (lean_obj_tag(v_a_3014_) == 0)
{
v___y_3000_ = v___y_3012_;
v___y_3001_ = v___y_3013_;
v_a_3002_ = v___y_3011_;
goto v___jp_2999_;
}
else
{
lean_dec_ref(v_a_3014_);
v___y_3000_ = v___y_3012_;
v___y_3001_ = v___y_3013_;
v_a_3002_ = v_hasTrace_2872_;
goto v___jp_2999_;
}
}
v___jp_3015_:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_a_3018_);
v___y_2985_ = v___y_3016_;
v___y_2986_ = v___y_3017_;
v_a_2987_ = v___x_3019_;
goto v___jp_2984_;
}
v___jp_3020_:
{
lean_object* v___x_3024_; double v___x_3025_; double v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3024_ = lean_io_get_num_heartbeats();
v___x_3025_ = lean_float_of_nat(v___y_3022_);
v___x_3026_ = lean_float_of_nat(v___x_3024_);
v___x_3027_ = lean_box_float(v___x_3025_);
v___x_3028_ = lean_box_float(v___x_3026_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_a_3023_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_2980_, v_hasTrace_2872_, v___x_2981_, v_options_2871_, v___x_2983_, v___y_3021_, v___f_2979_, v___x_3030_, v___y_2868_, v___y_2869_);
return v___x_3031_;
}
v___jp_3032_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_box(v_a_3035_);
v___x_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
v___y_3021_ = v___y_3033_;
v___y_3022_ = v___y_3034_;
v_a_3023_ = v___x_3037_;
goto v___jp_3020_;
}
v___jp_3038_:
{
if (lean_obj_tag(v_a_3043_) == 0)
{
v___y_3033_ = v___y_3041_;
v___y_3034_ = v___y_3042_;
v_a_3035_ = v___y_3040_;
goto v___jp_3032_;
}
else
{
lean_dec_ref(v_a_3043_);
v___y_3033_ = v___y_3041_;
v___y_3034_ = v___y_3042_;
v_a_3035_ = v___y_3039_;
goto v___jp_3032_;
}
}
v___jp_3044_:
{
if (lean_obj_tag(v_a_3048_) == 0)
{
uint8_t v___x_3049_; 
v___x_3049_ = 0;
v___y_3033_ = v___y_3046_;
v___y_3034_ = v___y_3047_;
v_a_3035_ = v___x_3049_;
goto v___jp_3032_;
}
else
{
lean_dec_ref(v_a_3048_);
v___y_3033_ = v___y_3046_;
v___y_3034_ = v___y_3047_;
v_a_3035_ = v___y_3045_;
goto v___jp_3032_;
}
}
v___jp_3050_:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_a_3053_);
v___y_3021_ = v___y_3051_;
v___y_3022_ = v___y_3052_;
v_a_3023_ = v___x_3054_;
goto v___jp_3020_;
}
v___jp_3055_:
{
if (lean_obj_tag(v___y_3058_) == 0)
{
lean_object* v_a_3059_; uint8_t v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___y_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___y_3058_);
v___x_3060_ = lean_unbox(v_a_3059_);
lean_dec(v_a_3059_);
v___y_3033_ = v___y_3056_;
v___y_3034_ = v___y_3057_;
v_a_3035_ = v___x_3060_;
goto v___jp_3032_;
}
else
{
lean_object* v_a_3061_; 
v_a_3061_ = lean_ctor_get(v___y_3058_, 0);
lean_inc(v_a_3061_);
lean_dec_ref(v___y_3058_);
v___y_3051_ = v___y_3056_;
v___y_3052_ = v___y_3057_;
v_a_3053_ = v_a_3061_;
goto v___jp_3050_;
}
}
v___jp_3062_:
{
lean_object* v___x_3063_; lean_object* v_a_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3063_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2869_);
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref(v___x_3063_);
v___x_3065_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3066_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_2871_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v_env_3069_; lean_object* v___x_3070_; 
lean_dec_ref(v___f_2866_);
v___x_3067_ = lean_io_mono_nanos_now();
v___x_3068_ = lean_st_ref_get(v___y_2869_);
v_env_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc_ref(v_env_3069_);
lean_dec(v___x_3068_);
lean_inc(v_name_2867_);
v___x_3070_ = l_Lean_Meta_declFromEqLikeName(v_env_3069_, v_name_2867_);
if (lean_obj_tag(v___x_3070_) == 1)
{
lean_object* v_val_3071_; lean_object* v_fst_3072_; lean_object* v_snd_3073_; lean_object* v___x_3074_; lean_object* v_env_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v_val_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_val_3071_);
lean_dec_ref(v___x_3070_);
v_fst_3072_ = lean_ctor_get(v_val_3071_, 0);
lean_inc_n(v_fst_3072_, 2);
v_snd_3073_ = lean_ctor_get(v_val_3071_, 1);
lean_inc_n(v_snd_3073_, 2);
lean_dec(v_val_3071_);
v___x_3074_ = lean_st_ref_get(v___y_2869_);
v_env_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc_ref(v_env_3075_);
lean_dec(v___x_3074_);
v___x_3076_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3075_, v_fst_3072_, v_snd_3073_);
v___x_3077_ = lean_name_eq(v_name_2867_, v___x_3076_);
lean_dec(v___x_3076_);
lean_dec(v_name_2867_);
if (v___x_3077_ == 0)
{
lean_dec(v_snd_3073_);
lean_dec(v_fst_3072_);
v___y_3000_ = v___x_3067_;
v___y_3001_ = v_a_3064_;
v_a_3002_ = v___x_3066_;
goto v___jp_2999_;
}
else
{
uint8_t v___x_3078_; 
lean_inc(v_snd_3073_);
v___x_3078_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3073_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3080_ = lean_string_dec_eq(v_snd_3073_, v___x_3079_);
lean_dec(v_snd_3073_);
if (v___x_3080_ == 0)
{
lean_dec(v_fst_3072_);
v___y_3000_ = v___x_3067_;
v___y_3001_ = v_a_3064_;
v_a_3002_ = v___x_3066_;
goto v___jp_2999_;
}
else
{
uint8_t v___x_3081_; uint8_t v___x_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; uint64_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3081_ = 1;
v___x_3082_ = 0;
v___x_3083_ = 2;
v___x_3084_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3084_, 0, v___x_3066_);
lean_ctor_set_uint8(v___x_3084_, 1, v___x_3066_);
lean_ctor_set_uint8(v___x_3084_, 2, v___x_3066_);
lean_ctor_set_uint8(v___x_3084_, 3, v___x_3066_);
lean_ctor_set_uint8(v___x_3084_, 4, v___x_3066_);
lean_ctor_set_uint8(v___x_3084_, 5, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 6, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 7, v___x_3066_);
lean_ctor_set_uint8(v___x_3084_, 8, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 9, v___x_3081_);
lean_ctor_set_uint8(v___x_3084_, 10, v___x_3082_);
lean_ctor_set_uint8(v___x_3084_, 11, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 12, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 13, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 14, v___x_3083_);
lean_ctor_set_uint8(v___x_3084_, 15, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 16, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 17, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3084_, 18, v_hasTrace_2872_);
v___x_3085_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3084_);
v___x_3086_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3086_, 0, v___x_3084_);
lean_ctor_set_uint64(v___x_3086_, sizeof(void*)*1, v___x_3085_);
v___x_3087_ = lean_box(1);
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3090_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3092_, 0, v___x_3086_);
lean_ctor_set(v___x_3092_, 1, v___x_3087_);
lean_ctor_set(v___x_3092_, 2, v___x_3089_);
lean_ctor_set(v___x_3092_, 3, v___x_3090_);
lean_ctor_set(v___x_3092_, 4, v___x_3091_);
lean_ctor_set(v___x_3092_, 5, v___x_3088_);
lean_ctor_set(v___x_3092_, 6, v___x_3091_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*7, v___x_3066_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*7 + 1, v___x_3066_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*7 + 2, v___x_3066_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*7 + 3, v_hasTrace_2872_);
v___x_3093_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3094_ = lean_st_mk_ref(v___x_3093_);
v___x_3095_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3072_, v_hasTrace_2872_, v___x_3092_, v___x_3094_, v___y_2868_, v___y_2869_);
lean_dec_ref(v___x_3092_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref(v___x_3095_);
v___x_3097_ = lean_st_ref_get(v___x_3094_);
lean_dec(v___x_3094_);
lean_dec(v___x_3097_);
v___y_3011_ = v___x_3066_;
v___y_3012_ = v___x_3067_;
v___y_3013_ = v_a_3064_;
v_a_3014_ = v_a_3096_;
goto v___jp_3010_;
}
else
{
lean_dec(v___x_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3098_; 
v_a_3098_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3098_);
lean_dec_ref(v___x_3095_);
v___y_3011_ = v___x_3066_;
v___y_3012_ = v___x_3067_;
v___y_3013_ = v_a_3064_;
v_a_3014_ = v_a_3098_;
goto v___jp_3010_;
}
else
{
lean_object* v_a_3099_; 
v_a_3099_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3099_);
lean_dec_ref(v___x_3095_);
v___y_3016_ = v___x_3067_;
v___y_3017_ = v_a_3064_;
v_a_3018_ = v_a_3099_;
goto v___jp_3015_;
}
}
}
}
else
{
uint8_t v___x_3100_; uint8_t v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; uint64_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v_snd_3073_);
v___x_3100_ = 1;
v___x_3101_ = 0;
v___x_3102_ = 2;
v___x_3103_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3103_, 0, v___x_3066_);
lean_ctor_set_uint8(v___x_3103_, 1, v___x_3066_);
lean_ctor_set_uint8(v___x_3103_, 2, v___x_3066_);
lean_ctor_set_uint8(v___x_3103_, 3, v___x_3066_);
lean_ctor_set_uint8(v___x_3103_, 4, v___x_3066_);
lean_ctor_set_uint8(v___x_3103_, 5, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 6, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 7, v___x_3066_);
lean_ctor_set_uint8(v___x_3103_, 8, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 9, v___x_3100_);
lean_ctor_set_uint8(v___x_3103_, 10, v___x_3101_);
lean_ctor_set_uint8(v___x_3103_, 11, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 12, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 13, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 14, v___x_3102_);
lean_ctor_set_uint8(v___x_3103_, 15, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 16, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 17, v_hasTrace_2872_);
lean_ctor_set_uint8(v___x_3103_, 18, v_hasTrace_2872_);
v___x_3104_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3103_);
v___x_3105_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set_uint64(v___x_3105_, sizeof(void*)*1, v___x_3104_);
v___x_3106_ = lean_box(1);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3109_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3111_, 0, v___x_3105_);
lean_ctor_set(v___x_3111_, 1, v___x_3106_);
lean_ctor_set(v___x_3111_, 2, v___x_3108_);
lean_ctor_set(v___x_3111_, 3, v___x_3109_);
lean_ctor_set(v___x_3111_, 4, v___x_3110_);
lean_ctor_set(v___x_3111_, 5, v___x_3107_);
lean_ctor_set(v___x_3111_, 6, v___x_3110_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7, v___x_3066_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 1, v___x_3066_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 2, v___x_3066_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 3, v_hasTrace_2872_);
v___x_3112_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3113_ = lean_st_mk_ref(v___x_3112_);
v___x_3114_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3072_, v___x_3111_, v___x_3113_, v___y_2868_, v___y_2869_);
lean_dec_ref(v___x_3111_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref(v___x_3114_);
v___x_3116_ = lean_st_ref_get(v___x_3113_);
lean_dec(v___x_3113_);
lean_dec(v___x_3116_);
v___y_3006_ = v___x_3066_;
v___y_3007_ = v___x_3067_;
v___y_3008_ = v_a_3064_;
v_a_3009_ = v_a_3115_;
goto v___jp_3005_;
}
else
{
lean_dec(v___x_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3117_; 
v_a_3117_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3117_);
lean_dec_ref(v___x_3114_);
v___y_3006_ = v___x_3066_;
v___y_3007_ = v___x_3067_;
v___y_3008_ = v_a_3064_;
v_a_3009_ = v_a_3117_;
goto v___jp_3005_;
}
else
{
lean_object* v_a_3118_; 
v_a_3118_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3118_);
lean_dec_ref(v___x_3114_);
v___y_3016_ = v___x_3067_;
v___y_3017_ = v_a_3064_;
v_a_3018_ = v_a_3118_;
goto v___jp_3015_;
}
}
}
}
}
else
{
lean_dec(v___x_3070_);
lean_dec(v_name_2867_);
v___y_3000_ = v___x_3067_;
v___y_3001_ = v_a_3064_;
v_a_3002_ = v___x_3066_;
goto v___jp_2999_;
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v_env_3121_; lean_object* v___x_3122_; 
v___x_3119_ = lean_io_get_num_heartbeats();
v___x_3120_ = lean_st_ref_get(v___y_2869_);
v_env_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc_ref(v_env_3121_);
lean_dec(v___x_3120_);
lean_inc(v_name_2867_);
v___x_3122_ = l_Lean_Meta_declFromEqLikeName(v_env_3121_, v_name_2867_);
if (lean_obj_tag(v___x_3122_) == 1)
{
lean_object* v_val_3123_; lean_object* v_fst_3124_; lean_object* v_snd_3125_; lean_object* v___x_3126_; lean_object* v_env_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v_val_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_val_3123_);
lean_dec_ref(v___x_3122_);
v_fst_3124_ = lean_ctor_get(v_val_3123_, 0);
lean_inc_n(v_fst_3124_, 2);
v_snd_3125_ = lean_ctor_get(v_val_3123_, 1);
lean_inc_n(v_snd_3125_, 2);
lean_dec(v_val_3123_);
v___x_3126_ = lean_st_ref_get(v___y_2869_);
v_env_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc_ref(v_env_3127_);
lean_dec(v___x_3126_);
v___x_3128_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3127_, v_fst_3124_, v_snd_3125_);
v___x_3129_ = lean_name_eq(v_name_2867_, v___x_3128_);
lean_dec(v___x_3128_);
lean_dec(v_name_2867_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec(v_snd_3125_);
lean_dec(v_fst_3124_);
v___x_3130_ = lean_box(0);
lean_inc(v___y_2869_);
lean_inc_ref(v___y_2868_);
v___x_3131_ = lean_apply_4(v___f_2866_, v___x_3130_, v___y_2868_, v___y_2869_, lean_box(0));
v___y_3056_ = v_a_3064_;
v___y_3057_ = v___x_3119_;
v___y_3058_ = v___x_3131_;
goto v___jp_3055_;
}
else
{
uint8_t v___x_3132_; 
lean_inc(v_snd_3125_);
v___x_3132_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3125_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3133_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3134_ = lean_string_dec_eq(v_snd_3125_, v___x_3133_);
lean_dec(v_snd_3125_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec(v_fst_3124_);
v___x_3135_ = lean_box(0);
lean_inc(v___y_2869_);
lean_inc_ref(v___y_2868_);
v___x_3136_ = lean_apply_4(v___f_2866_, v___x_3135_, v___y_2868_, v___y_2869_, lean_box(0));
v___y_3056_ = v_a_3064_;
v___y_3057_ = v___x_3119_;
v___y_3058_ = v___x_3136_;
goto v___jp_3055_;
}
else
{
uint8_t v___x_3137_; uint8_t v___x_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; uint64_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec_ref(v___f_2866_);
v___x_3137_ = 1;
v___x_3138_ = 0;
v___x_3139_ = 2;
v___x_3140_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3140_, 0, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 1, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 2, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 3, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 4, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 5, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 6, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 7, v___x_3132_);
lean_ctor_set_uint8(v___x_3140_, 8, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 9, v___x_3137_);
lean_ctor_set_uint8(v___x_3140_, 10, v___x_3138_);
lean_ctor_set_uint8(v___x_3140_, 11, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 12, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 13, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 14, v___x_3139_);
lean_ctor_set_uint8(v___x_3140_, 15, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 16, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 17, v___x_3066_);
lean_ctor_set_uint8(v___x_3140_, 18, v___x_3066_);
v___x_3141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set_uint64(v___x_3142_, sizeof(void*)*1, v___x_3141_);
v___x_3143_ = lean_box(1);
v___x_3144_ = lean_unsigned_to_nat(0u);
v___x_3145_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3146_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3147_ = lean_box(0);
v___x_3148_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3148_, 0, v___x_3142_);
lean_ctor_set(v___x_3148_, 1, v___x_3143_);
lean_ctor_set(v___x_3148_, 2, v___x_3145_);
lean_ctor_set(v___x_3148_, 3, v___x_3146_);
lean_ctor_set(v___x_3148_, 4, v___x_3147_);
lean_ctor_set(v___x_3148_, 5, v___x_3144_);
lean_ctor_set(v___x_3148_, 6, v___x_3147_);
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*7, v___x_3132_);
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*7 + 1, v___x_3132_);
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*7 + 2, v___x_3132_);
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*7 + 3, v___x_3066_);
v___x_3149_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3150_ = lean_st_mk_ref(v___x_3149_);
v___x_3151_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3124_, v___x_3066_, v___x_3148_, v___x_3150_, v___y_2868_, v___y_2869_);
lean_dec_ref(v___x_3148_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref(v___x_3151_);
v___x_3153_ = lean_st_ref_get(v___x_3150_);
lean_dec(v___x_3150_);
lean_dec(v___x_3153_);
v___y_3039_ = v___x_3066_;
v___y_3040_ = v___x_3132_;
v___y_3041_ = v_a_3064_;
v___y_3042_ = v___x_3119_;
v_a_3043_ = v_a_3152_;
goto v___jp_3038_;
}
else
{
lean_dec(v___x_3150_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3154_; 
v_a_3154_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3154_);
lean_dec_ref(v___x_3151_);
v___y_3039_ = v___x_3066_;
v___y_3040_ = v___x_3132_;
v___y_3041_ = v_a_3064_;
v___y_3042_ = v___x_3119_;
v_a_3043_ = v_a_3154_;
goto v___jp_3038_;
}
else
{
lean_object* v_a_3155_; 
v_a_3155_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3155_);
lean_dec_ref(v___x_3151_);
v___y_3051_ = v_a_3064_;
v___y_3052_ = v___x_3119_;
v_a_3053_ = v_a_3155_;
goto v___jp_3050_;
}
}
}
}
else
{
uint8_t v___x_3156_; uint8_t v___x_3157_; uint8_t v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; uint64_t v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec(v_snd_3125_);
lean_dec_ref(v___f_2866_);
v___x_3156_ = 0;
v___x_3157_ = 1;
v___x_3158_ = 0;
v___x_3159_ = 2;
v___x_3160_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3160_, 0, v___x_3156_);
lean_ctor_set_uint8(v___x_3160_, 1, v___x_3156_);
lean_ctor_set_uint8(v___x_3160_, 2, v___x_3156_);
lean_ctor_set_uint8(v___x_3160_, 3, v___x_3156_);
lean_ctor_set_uint8(v___x_3160_, 4, v___x_3156_);
lean_ctor_set_uint8(v___x_3160_, 5, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 6, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 7, v___x_3156_);
lean_ctor_set_uint8(v___x_3160_, 8, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 9, v___x_3157_);
lean_ctor_set_uint8(v___x_3160_, 10, v___x_3158_);
lean_ctor_set_uint8(v___x_3160_, 11, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 12, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 13, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 14, v___x_3159_);
lean_ctor_set_uint8(v___x_3160_, 15, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 16, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 17, v___x_3066_);
lean_ctor_set_uint8(v___x_3160_, 18, v___x_3066_);
v___x_3161_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set_uint64(v___x_3162_, sizeof(void*)*1, v___x_3161_);
v___x_3163_ = lean_box(1);
v___x_3164_ = lean_unsigned_to_nat(0u);
v___x_3165_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3166_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3167_ = lean_box(0);
v___x_3168_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3168_, 0, v___x_3162_);
lean_ctor_set(v___x_3168_, 1, v___x_3163_);
lean_ctor_set(v___x_3168_, 2, v___x_3165_);
lean_ctor_set(v___x_3168_, 3, v___x_3166_);
lean_ctor_set(v___x_3168_, 4, v___x_3167_);
lean_ctor_set(v___x_3168_, 5, v___x_3164_);
lean_ctor_set(v___x_3168_, 6, v___x_3167_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*7, v___x_3156_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*7 + 1, v___x_3156_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*7 + 2, v___x_3156_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*7 + 3, v___x_3066_);
v___x_3169_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3170_ = lean_st_mk_ref(v___x_3169_);
v___x_3171_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3124_, v___x_3168_, v___x_3170_, v___y_2868_, v___y_2869_);
lean_dec_ref(v___x_3168_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = lean_st_ref_get(v___x_3170_);
lean_dec(v___x_3170_);
lean_dec(v___x_3173_);
v___y_3045_ = v___x_3066_;
v___y_3046_ = v_a_3064_;
v___y_3047_ = v___x_3119_;
v_a_3048_ = v_a_3172_;
goto v___jp_3044_;
}
else
{
lean_dec(v___x_3170_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3174_; 
v_a_3174_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3174_);
lean_dec_ref(v___x_3171_);
v___y_3045_ = v___x_3066_;
v___y_3046_ = v_a_3064_;
v___y_3047_ = v___x_3119_;
v_a_3048_ = v_a_3174_;
goto v___jp_3044_;
}
else
{
lean_object* v_a_3175_; 
v_a_3175_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3175_);
lean_dec_ref(v___x_3171_);
v___y_3051_ = v_a_3064_;
v___y_3052_ = v___x_3119_;
v_a_3053_ = v_a_3175_;
goto v___jp_3050_;
}
}
}
}
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec(v___x_3122_);
lean_dec(v_name_2867_);
v___x_3176_ = lean_box(0);
lean_inc(v___y_2869_);
lean_inc_ref(v___y_2868_);
v___x_3177_ = lean_apply_4(v___f_2866_, v___x_3176_, v___y_2868_, v___y_2869_, lean_box(0));
v___y_3056_ = v_a_3064_;
v___y_3057_ = v___x_3119_;
v___y_3058_ = v___x_3177_;
goto v___jp_3055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3285_, lean_object* v_name_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3285_, v_name_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
return v_res_3290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = lean_unsigned_to_nat(3137104340u);
v___x_3335_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3336_ = l_Lean_Name_num___override(v___x_3335_, v___x_3334_);
return v___x_3336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3339_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3340_ = l_Lean_Name_str___override(v___x_3339_, v___x_3338_);
return v___x_3340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3343_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3344_ = l_Lean_Name_str___override(v___x_3343_, v___x_3342_);
return v___x_3344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = lean_unsigned_to_nat(2u);
v___x_3346_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3347_ = l_Lean_Name_num___override(v___x_3346_, v___x_3345_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3349_; lean_object* v___x_3350_; 
v___f_3349_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3350_ = l_Lean_registerReservedNameAction(v___f_3349_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v___x_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_dec_ref(v___x_3350_);
v___x_3351_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_3352_ = 0;
v___x_3353_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3354_ = l_Lean_registerTraceClass(v___x_3351_, v___x_3352_, v___x_3353_);
return v___x_3354_;
}
else
{
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b1_3357_, lean_object* v_x_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_3358_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_00_u03b1_3363_, lean_object* v_x_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b1_3363_, v_x_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
return v_res_3368_;
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
