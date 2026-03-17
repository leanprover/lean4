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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isEqnReservedNameSuffix___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ReservedNameAction"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 245, 189, 90, 36, 141, 82, 229)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(lean_object* v___x_102_, uint8_t v___x_103_, lean_object* v___x_104_, lean_object* v___x_105_, lean_object* v_s_106_, lean_object* v_a_107_, lean_object* v_b_108_){
_start:
{
lean_object* v_startInclusive_109_; lean_object* v_endExclusive_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_startInclusive_109_ = lean_ctor_get(v___x_104_, 1);
v_endExclusive_110_ = lean_ctor_get(v___x_104_, 2);
v___x_111_ = lean_nat_sub(v_endExclusive_110_, v_startInclusive_109_);
v___x_112_ = lean_nat_dec_eq(v_a_107_, v___x_111_);
lean_dec(v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v_snd_113_; lean_object* v_snd_114_; lean_object* v_fst_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_178_; 
v_snd_113_ = lean_ctor_get(v_b_108_, 1);
lean_inc(v_snd_113_);
v_snd_114_ = lean_ctor_get(v_snd_113_, 1);
lean_inc(v_snd_114_);
v_fst_115_ = lean_ctor_get(v_b_108_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_b_108_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; 
v_unused_179_ = lean_ctor_get(v_b_108_, 1);
lean_dec(v_unused_179_);
v___x_117_ = v_b_108_;
v_isShared_118_ = v_isSharedCheck_178_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_fst_115_);
lean_dec(v_b_108_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_178_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_fst_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_176_; 
v_fst_119_ = lean_ctor_get(v_snd_113_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v_snd_113_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v_snd_113_, 1);
lean_dec(v_unused_177_);
v___x_121_ = v_snd_113_;
v_isShared_122_ = v_isSharedCheck_176_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_fst_119_);
lean_dec(v_snd_113_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_176_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_snd_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_174_; 
v_snd_123_ = lean_ctor_get(v_snd_114_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_snd_114_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v_snd_114_, 0);
lean_dec(v_unused_175_);
v___x_125_ = v_snd_114_;
v_isShared_126_ = v_isSharedCheck_174_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_snd_123_);
lean_dec(v_snd_114_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_174_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint32_t v___x_132_; uint8_t v___y_134_; uint8_t v___y_135_; uint8_t v___y_153_; uint8_t v___y_154_; uint8_t v___y_159_; uint8_t v___y_160_; uint8_t v___y_165_; uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_nat_dec_eq(v___x_102_, v___x_127_);
v___x_129_ = lean_nat_add(v___x_105_, v_a_107_);
lean_dec(v_a_107_);
v___x_130_ = lean_string_utf8_next_fast(v_s_106_, v___x_129_);
v___x_131_ = lean_nat_sub(v___x_130_, v___x_105_);
v___x_132_ = lean_string_utf8_get_fast(v_s_106_, v___x_129_);
lean_dec(v___x_129_);
v___x_170_ = 48;
v___x_171_ = lean_uint32_dec_le(v___x_170_, v___x_132_);
if (v___x_171_ == 0)
{
v___y_165_ = v___x_171_;
goto v___jp_164_;
}
else
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 57;
v___x_173_ = lean_uint32_dec_le(v___x_132_, v___x_172_);
v___y_165_ = v___x_173_;
goto v___jp_164_;
}
v___jp_133_:
{
uint32_t v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_136_ = 95;
v___x_137_ = lean_uint32_dec_eq(v___x_132_, v___x_136_);
v___x_138_ = lean_box(v___y_134_);
v___x_139_ = lean_box(v___y_135_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_139_);
lean_ctor_set(v___x_125_, 0, v___x_138_);
v___x_141_ = v___x_125_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_151_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_box(v___x_137_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_141_);
lean_ctor_set(v___x_121_, 0, v___x_142_);
v___x_144_ = v___x_121_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_141_);
v___x_144_ = v_reuseFailAlloc_150_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = lean_box(v___x_128_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_144_);
lean_ctor_set(v___x_117_, 0, v___x_145_);
v___x_147_ = v___x_117_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_144_);
v___x_147_ = v_reuseFailAlloc_149_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
v_a_107_ = v___x_131_;
v_b_108_ = v___x_147_;
goto _start;
}
}
}
}
v___jp_152_:
{
uint8_t v___x_155_; 
v___x_155_ = lean_unbox(v_fst_119_);
lean_dec(v_fst_119_);
if (v___x_155_ == 0)
{
v___y_134_ = v___y_153_;
v___y_135_ = v___y_154_;
goto v___jp_133_;
}
else
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 95;
v___x_157_ = lean_uint32_dec_eq(v___x_132_, v___x_156_);
if (v___x_157_ == 0)
{
v___y_134_ = v___y_153_;
v___y_135_ = v___y_154_;
goto v___jp_133_;
}
else
{
v___y_134_ = v___y_153_;
v___y_135_ = v___x_128_;
goto v___jp_133_;
}
}
}
v___jp_158_:
{
uint8_t v___x_161_; 
v___x_161_ = lean_unbox(v_fst_115_);
lean_dec(v_fst_115_);
if (v___x_161_ == 0)
{
v___y_153_ = v___y_159_;
v___y_154_ = v___y_160_;
goto v___jp_152_;
}
else
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 95;
v___x_163_ = lean_uint32_dec_eq(v___x_132_, v___x_162_);
if (v___x_163_ == 0)
{
v___y_153_ = v___y_159_;
v___y_154_ = v___y_160_;
goto v___jp_152_;
}
else
{
if (v___x_128_ == 0)
{
lean_dec(v_fst_119_);
v___y_134_ = v___y_159_;
v___y_135_ = v___x_128_;
goto v___jp_133_;
}
else
{
v___y_153_ = v___y_159_;
v___y_154_ = v___x_128_;
goto v___jp_152_;
}
}
}
}
v___jp_164_:
{
uint8_t v___x_166_; 
v___x_166_ = lean_unbox(v_snd_123_);
if (v___x_166_ == 0)
{
uint8_t v___x_167_; 
lean_dec(v_fst_119_);
lean_dec(v_fst_115_);
v___x_167_ = lean_unbox(v_snd_123_);
lean_dec(v_snd_123_);
v___y_134_ = v___y_165_;
v___y_135_ = v___x_167_;
goto v___jp_133_;
}
else
{
lean_dec(v_snd_123_);
if (v___y_165_ == 0)
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 95;
v___x_169_ = lean_uint32_dec_eq(v___x_132_, v___x_168_);
if (v___x_169_ == 0)
{
lean_dec(v_fst_119_);
lean_dec(v_fst_115_);
v___y_134_ = v___y_165_;
v___y_135_ = v___x_169_;
goto v___jp_133_;
}
else
{
v___y_159_ = v___y_165_;
v___y_160_ = v___x_169_;
goto v___jp_158_;
}
}
else
{
v___y_159_ = v___y_165_;
v___y_160_ = v___x_103_;
goto v___jp_158_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_107_);
return v_b_108_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg___boxed(lean_object* v___x_180_, lean_object* v___x_181_, lean_object* v___x_182_, lean_object* v___x_183_, lean_object* v_s_184_, lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
uint8_t v___x_613__boxed_187_; lean_object* v_res_188_; 
v___x_613__boxed_187_ = lean_unbox(v___x_181_);
v_res_188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(v___x_180_, v___x_613__boxed_187_, v___x_182_, v___x_183_, v_s_184_, v_a_185_, v_b_186_);
lean_dec_ref(v_s_184_);
lean_dec(v___x_183_);
lean_dec_ref(v___x_182_);
lean_dec(v___x_180_);
return v_res_188_;
}
}
static lean_object* _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_190_ = lean_string_utf8_byte_size(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_192_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_193_ = lean_string_utf8_byte_size(v_s_191_);
v___x_194_ = lean_obj_once(&l_Lean_Meta_isEqnReservedNameSuffix___closed__0, &l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0);
v___x_195_ = lean_nat_dec_le(v___x_194_, v___x_193_);
if (v___x_195_ == 0)
{
lean_dec_ref(v_s_191_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_string_memcmp(v_s_191_, v___x_192_, v___x_196_, v___x_196_, v___x_194_);
if (v___x_197_ == 0)
{
lean_dec_ref(v_s_191_);
return v___x_197_;
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_198_ = lean_unsigned_to_nat(3u);
lean_inc_ref(v_s_191_);
v___x_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_199_, 0, v_s_191_);
lean_ctor_set(v___x_199_, 1, v___x_196_);
lean_ctor_set(v___x_199_, 2, v___x_193_);
v___x_200_ = l_String_Slice_Pos_nextn(v___x_199_, v___x_196_, v___x_198_);
lean_dec_ref(v___x_199_);
v___x_201_ = lean_nat_sub(v___x_193_, v___x_200_);
v___x_202_ = lean_nat_dec_eq(v___x_201_, v___x_196_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_result_212_; lean_object* v_snd_213_; lean_object* v_snd_214_; lean_object* v_snd_215_; uint8_t v___x_216_; 
lean_inc(v___x_200_);
lean_inc_ref(v_s_191_);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v_s_191_);
lean_ctor_set(v___x_203_, 1, v___x_200_);
lean_ctor_set(v___x_203_, 2, v___x_193_);
v___x_204_ = lean_box(v___x_202_);
v___x_205_ = lean_box(v___x_197_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_box(v___x_202_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
v___x_209_ = lean_box(v___x_197_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
v___x_211_ = l_String_Slice_positions(v___x_203_);
v_result_212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(v___x_201_, v___x_197_, v___x_203_, v___x_200_, v_s_191_, v___x_211_, v___x_210_);
lean_dec_ref(v_s_191_);
lean_dec(v___x_200_);
lean_dec_ref(v___x_203_);
lean_dec(v___x_201_);
v_snd_213_ = lean_ctor_get(v_result_212_, 1);
lean_inc(v_snd_213_);
lean_dec_ref(v_result_212_);
v_snd_214_ = lean_ctor_get(v_snd_213_, 1);
lean_inc(v_snd_214_);
lean_dec(v_snd_213_);
v_snd_215_ = lean_ctor_get(v_snd_214_, 1);
v___x_216_ = lean_unbox(v_snd_215_);
if (v___x_216_ == 0)
{
lean_dec(v_snd_214_);
return v___x_202_;
}
else
{
lean_object* v_fst_217_; uint8_t v___x_218_; 
v_fst_217_ = lean_ctor_get(v_snd_214_, 0);
lean_inc(v_fst_217_);
lean_dec(v_snd_214_);
v___x_218_ = lean_unbox(v_fst_217_);
lean_dec(v_fst_217_);
return v___x_218_;
}
}
else
{
uint8_t v___x_219_; 
lean_dec(v___x_201_);
lean_dec(v___x_200_);
lean_dec_ref(v_s_191_);
v___x_219_ = 0;
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0(lean_object* v___x_223_, uint8_t v___x_224_, lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v_s_227_, lean_object* v_inst_228_, lean_object* v_R_229_, lean_object* v_a_230_, lean_object* v_b_231_, lean_object* v_c_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(v___x_223_, v___x_224_, v___x_225_, v___x_226_, v_s_227_, v_a_230_, v_b_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___boxed(lean_object* v___x_234_, lean_object* v___x_235_, lean_object* v___x_236_, lean_object* v___x_237_, lean_object* v_s_238_, lean_object* v_inst_239_, lean_object* v_R_240_, lean_object* v_a_241_, lean_object* v_b_242_, lean_object* v_c_243_){
_start:
{
uint8_t v___x_817__boxed_244_; lean_object* v_res_245_; 
v___x_817__boxed_244_ = lean_unbox(v___x_235_);
v_res_245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0(v___x_234_, v___x_817__boxed_244_, v___x_236_, v___x_237_, v_s_238_, v_inst_239_, v_R_240_, v_a_241_, v_b_242_, v_c_243_);
lean_dec_ref(v_s_238_);
lean_dec(v___x_237_);
lean_dec_ref(v___x_236_);
lean_dec(v___x_234_);
return v_res_245_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_250_){
_start:
{
uint8_t v___y_252_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_255_ = lean_string_dec_eq(v_s_250_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_257_ = lean_string_dec_eq(v_s_250_, v___x_256_);
v___y_252_ = v___x_257_;
goto v___jp_251_;
}
else
{
v___y_252_ = v___x_255_;
goto v___jp_251_;
}
v___jp_251_:
{
if (v___y_252_ == 0)
{
uint8_t v___x_253_; 
v___x_253_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_250_);
return v___x_253_;
}
else
{
lean_dec_ref(v_s_250_);
return v___y_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_Meta_isEqnLikeSuffix(v_s_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_264_, lean_object* v_env_265_, lean_object* v_as_x27_266_, lean_object* v_b_267_){
_start:
{
if (lean_obj_tag(v_as_x27_266_) == 0)
{
lean_dec_ref(v_env_265_);
lean_dec_ref(v_str_264_);
return v_b_267_;
}
else
{
lean_object* v_head_268_; lean_object* v_tail_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_289_; 
lean_dec_ref(v_b_267_);
v_head_268_ = lean_ctor_get(v_as_x27_266_, 0);
v_tail_269_ = lean_ctor_get(v_as_x27_266_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_as_x27_266_);
if (v_isSharedCheck_289_ == 0)
{
v___x_271_ = v_as_x27_266_;
v_isShared_272_ = v_isSharedCheck_289_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_tail_269_);
lean_inc(v_head_268_);
lean_dec(v_as_x27_266_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_289_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___y_276_; uint8_t v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_273_ = lean_box(0);
v___x_274_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_284_ = 0;
lean_inc_ref(v_env_265_);
v___x_285_ = l_Lean_Environment_setExporting(v_env_265_, v___x_284_);
lean_inc(v_head_268_);
v___x_286_ = l_Lean_Environment_isSafeDefinition(v___x_285_, v_head_268_);
if (v___x_286_ == 0)
{
v___y_276_ = v___x_286_;
goto v___jp_275_;
}
else
{
uint8_t v___x_287_; 
lean_inc(v_head_268_);
lean_inc_ref(v_env_265_);
v___x_287_ = lean_is_matcher(v_env_265_, v_head_268_);
if (v___x_287_ == 0)
{
v___y_276_ = v___x_286_;
goto v___jp_275_;
}
else
{
lean_del_object(v___x_271_);
lean_dec(v_head_268_);
v_as_x27_266_ = v_tail_269_;
v_b_267_ = v___x_274_;
goto _start;
}
}
v___jp_275_:
{
if (v___y_276_ == 0)
{
lean_del_object(v___x_271_);
lean_dec(v_head_268_);
v_as_x27_266_ = v_tail_269_;
v_b_267_ = v___x_274_;
goto _start;
}
else
{
lean_object* v___x_279_; 
lean_dec(v_tail_269_);
lean_dec_ref(v_env_265_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 0);
lean_ctor_set(v___x_271_, 1, v_str_264_);
v___x_279_ = v___x_271_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_head_268_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_str_264_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_273_);
return v___x_282_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_290_, lean_object* v_name_291_){
_start:
{
if (lean_obj_tag(v_name_291_) == 1)
{
lean_object* v_pre_292_; lean_object* v_str_293_; uint8_t v___x_294_; 
v_pre_292_ = lean_ctor_get(v_name_291_, 0);
lean_inc(v_pre_292_);
v_str_293_ = lean_ctor_get(v_name_291_, 1);
lean_inc_ref(v_str_293_);
lean_dec_ref(v_name_291_);
lean_inc_ref(v_str_293_);
v___x_294_ = l_Lean_Meta_isEqnLikeSuffix(v_str_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_dec_ref(v_str_293_);
lean_dec(v_pre_292_);
lean_dec_ref(v_env_290_);
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_fst_303_; 
lean_inc(v_pre_292_);
v___x_296_ = l_Lean_privateToUserName(v_pre_292_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v_pre_292_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_box(0);
v___x_301_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_302_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_293_, v_env_290_, v___x_299_, v___x_301_);
v_fst_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_fst_303_);
lean_dec_ref(v___x_302_);
if (lean_obj_tag(v_fst_303_) == 0)
{
return v___x_300_;
}
else
{
lean_object* v_val_304_; 
v_val_304_ = lean_ctor_get(v_fst_303_, 0);
lean_inc(v_val_304_);
lean_dec_ref(v_fst_303_);
return v_val_304_;
}
}
}
else
{
lean_object* v___x_305_; 
lean_dec(v_name_291_);
lean_dec_ref(v_env_290_);
v___x_305_ = lean_box(0);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_306_, lean_object* v_env_307_, lean_object* v_as_308_, lean_object* v_as_x27_309_, lean_object* v_b_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_306_, v_env_307_, v_as_x27_309_, v_b_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_313_, lean_object* v_env_314_, lean_object* v_as_315_, lean_object* v_as_x27_316_, lean_object* v_b_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_313_, v_env_314_, v_as_315_, v_as_x27_316_, v_b_317_, v_a_318_);
lean_dec(v_as_315_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_320_, lean_object* v_declName_321_, lean_object* v_suffix_322_){
_start:
{
lean_object* v___x_326_; uint8_t v_isModule_327_; 
v___x_326_ = l_Lean_Environment_header(v_env_320_);
v_isModule_327_ = lean_ctor_get_uint8(v___x_326_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_326_);
if (v_isModule_327_ == 0)
{
lean_object* v_name_328_; 
lean_dec_ref(v_env_320_);
v_name_328_ = l_Lean_Name_str___override(v_declName_321_, v_suffix_322_);
return v_name_328_;
}
else
{
uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = 0;
lean_inc_ref(v_env_320_);
v___x_330_ = l_Lean_Environment_setExporting(v_env_320_, v_isModule_327_);
lean_inc(v_declName_321_);
v___x_331_ = l_Lean_Environment_find_x3f(v___x_330_, v_declName_321_, v___x_329_);
if (lean_obj_tag(v___x_331_) == 0)
{
goto v___jp_323_;
}
else
{
lean_object* v_val_332_; uint8_t v___x_333_; 
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref(v___x_331_);
v___x_333_ = l_Lean_ConstantInfo_hasValue(v_val_332_, v___x_329_);
lean_dec(v_val_332_);
if (v___x_333_ == 0)
{
goto v___jp_323_;
}
else
{
lean_object* v_name_334_; 
lean_dec_ref(v_env_320_);
v_name_334_ = l_Lean_Name_str___override(v_declName_321_, v_suffix_322_);
return v_name_334_;
}
}
}
v___jp_323_:
{
lean_object* v_name_324_; lean_object* v___x_325_; 
v_name_324_ = l_Lean_Name_str___override(v_declName_321_, v_suffix_322_);
v___x_325_ = l_Lean_mkPrivateName(v_env_320_, v_name_324_);
lean_dec_ref(v_env_320_);
return v___x_325_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_335_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_ctor_set(v___x_340_, 2, v___x_339_);
lean_ctor_set(v___x_340_, 3, v___x_338_);
lean_ctor_set(v___x_340_, 4, v___x_338_);
lean_ctor_set(v___x_340_, 5, v___x_338_);
lean_ctor_set(v___x_340_, 6, v___x_338_);
lean_ctor_set(v___x_340_, 7, v___x_338_);
lean_ctor_set(v___x_340_, 8, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_unsigned_to_nat(32u);
v___x_342_ = lean_mk_empty_array_with_capacity(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((size_t)5ULL);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_unsigned_to_nat(32u);
v___x_347_ = lean_mk_empty_array_with_capacity(v___x_346_);
v___x_348_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_349_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_345_);
lean_ctor_set(v___x_349_, 3, v___x_345_);
lean_ctor_set_usize(v___x_349_, 4, v___x_344_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = lean_box(1);
v___x_351_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v_env_359_; lean_object* v_options_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_358_ = lean_st_ref_get(v___y_356_);
v_env_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc_ref(v_env_359_);
lean_dec(v___x_358_);
v_options_360_ = lean_ctor_get(v___y_355_, 2);
v___x_361_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_362_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_360_);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v_env_359_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
lean_ctor_set(v___x_363_, 3, v_options_360_);
v___x_364_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_msgData_354_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_ref_375_; lean_object* v___x_376_; lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_385_; 
v_ref_375_ = lean_ctor_get(v___y_372_, 5);
v___x_376_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_371_, v___y_372_, v___y_373_);
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_385_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_inc(v_ref_375_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_ref_375_);
lean_ctor_set(v___x_381_, 1, v_a_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 1);
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_390_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_400_, lean_object* v_reservedName_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_405_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_406_ = 0;
v___x_407_ = l_Lean_MessageData_ofConstName(v_declName_400_, v___x_406_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_405_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = 1;
v___x_412_ = l_Lean_MessageData_ofConstName(v_reservedName_401_, v___x_411_);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_410_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_415_, v___y_402_, v___y_403_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_417_, lean_object* v_reservedName_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_417_, v_reservedName_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_423_, lean_object* v_suffix_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; lean_object* v_env_429_; lean_object* v_reservedName_430_; uint8_t v___x_431_; uint8_t v___x_432_; 
v___x_428_ = lean_st_ref_get(v___y_426_);
v_env_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_ref(v_env_429_);
lean_dec(v___x_428_);
lean_inc(v_declName_423_);
v_reservedName_430_ = l_Lean_Name_str___override(v_declName_423_, v_suffix_424_);
v___x_431_ = 1;
lean_inc(v_reservedName_430_);
v___x_432_ = l_Lean_Environment_contains(v_env_429_, v_reservedName_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_reservedName_430_);
lean_dec(v_declName_423_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_423_, v_reservedName_430_, v___y_425_, v___y_426_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_436_, lean_object* v_suffix_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_436_, v_suffix_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_442_);
v___x_447_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_442_, v___x_446_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref(v___x_447_);
v___x_448_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_442_);
v___x_449_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_442_, v___x_448_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref(v___x_449_);
v___x_450_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_451_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_442_, v___x_450_, v_a_443_, v_a_444_);
return v___x_451_;
}
else
{
lean_dec(v_declName_442_);
return v___x_449_;
}
}
else
{
lean_dec(v_declName_442_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_457_, lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_458_, v___y_459_, v___y_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_463_, v_msg_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_468_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_469_, lean_object* v_n_470_){
_start:
{
lean_object* v___x_471_; 
lean_inc(v_n_470_);
lean_inc_ref(v_env_469_);
v___x_471_ = l_Lean_Meta_declFromEqLikeName(v_env_469_, v_n_470_);
if (lean_obj_tag(v___x_471_) == 1)
{
lean_object* v_val_472_; lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref(v___x_471_);
v_fst_473_ = lean_ctor_get(v_val_472_, 0);
lean_inc(v_fst_473_);
v_snd_474_ = lean_ctor_get(v_val_472_, 1);
lean_inc(v_snd_474_);
lean_dec(v_val_472_);
v___x_475_ = l_Lean_Meta_mkEqLikeNameFor(v_env_469_, v_fst_473_, v_snd_474_);
v___x_476_ = lean_name_eq(v_n_470_, v___x_475_);
lean_dec(v___x_475_);
lean_dec(v_n_470_);
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
lean_dec(v___x_471_);
lean_dec(v_n_470_);
lean_dec_ref(v_env_469_);
v___x_477_ = 0;
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_478_, lean_object* v_n_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_478_, v_n_479_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_484_; lean_object* v___x_485_; 
v___f_484_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_485_ = l_Lean_registerReservedNamePredicate(v___f_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
v___x_490_ = lean_st_mk_ref(v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_493_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_496_ = lean_mk_io_user_error(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_initializing();
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_516_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_516_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_516_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_516_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
uint8_t v___x_504_; 
v___x_504_ = lean_unbox(v_a_500_);
lean_dec(v_a_500_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec_ref(v_f_497_);
v___x_505_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 1);
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_509_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_510_ = lean_st_ref_take(v___x_509_);
v___x_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_511_, 0, v_f_497_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_st_ref_set(v___x_509_, v___x_511_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_512_);
v___x_514_ = v___x_502_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_f_497_);
v_a_517_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_499_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_499_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_registerGetEqnsFn(v_f_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_538_; lean_object* v_env_539_; uint8_t v___x_540_; lean_object* v___x_541_; 
v___x_538_ = lean_st_ref_get(v_a_532_);
v_env_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc_ref(v_env_539_);
lean_dec(v___x_538_);
v___x_540_ = 0;
lean_inc(v_declName_528_);
v___x_541_ = l_Lean_Environment_findAsync_x3f(v_env_539_, v_declName_528_, v___x_540_);
if (lean_obj_tag(v___x_541_) == 1)
{
lean_object* v_val_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_573_; 
v_val_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_573_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_573_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_val_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_573_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
uint8_t v_kind_546_; 
v_kind_546_ = lean_ctor_get_uint8(v_val_542_, sizeof(void*)*3);
if (v_kind_546_ == 0)
{
lean_object* v_sig_547_; lean_object* v___x_548_; lean_object* v_env_549_; uint8_t v___x_550_; 
v_sig_547_ = lean_ctor_get(v_val_542_, 1);
lean_inc_ref(v_sig_547_);
lean_dec(v_val_542_);
v___x_548_ = lean_st_ref_get(v_a_532_);
v_env_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc_ref(v_env_549_);
lean_dec(v___x_548_);
v___x_550_ = lean_is_matcher(v_env_549_, v_declName_528_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v_type_552_; lean_object* v___x_553_; 
lean_del_object(v___x_544_);
v___x_551_ = lean_task_get_own(v_sig_547_);
v_type_552_ = lean_ctor_get(v___x_551_, 2);
lean_inc_ref(v_type_552_);
lean_dec(v___x_551_);
v___x_553_ = l_Lean_Meta_isProp(v_type_552_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_568_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_568_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_568_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_568_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
uint8_t v___x_558_; 
v___x_558_ = lean_unbox(v_a_554_);
lean_dec(v_a_554_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_559_ = 1;
v___x_560_ = lean_box(v___x_559_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_560_);
v___x_562_ = v___x_556_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = lean_box(v___x_550_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_564_);
v___x_566_ = v___x_556_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
return v___x_553_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_dec_ref(v_sig_547_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
v___x_569_ = lean_box(v___x_540_);
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 0);
lean_ctor_set(v___x_544_, 0, v___x_569_);
v___x_571_ = v___x_544_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_del_object(v___x_544_);
lean_dec(v_val_542_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_declName_528_);
goto v___jp_534_;
}
}
}
else
{
lean_dec(v___x_541_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_declName_528_);
goto v___jp_534_;
}
v___jp_534_:
{
uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = 0;
v___x_536_ = lean_box(v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
return v_res_580_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_581_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_589_);
return v_res_591_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_592_; lean_object* v___f_593_; 
v___x_592_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_593_, 0, v___x_592_);
return v___f_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___f_595_ = lean_obj_once(&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_596_ = lean_box(0);
v___x_597_ = lean_box(1);
v___x_598_ = l_Lean_registerEnvExtension___redArg(v___f_595_, v___x_596_, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; lean_object* v_env_605_; lean_object* v_toConstantVal_606_; lean_object* v_value_607_; lean_object* v_all_608_; uint8_t v___y_610_; lean_object* v_type_618_; uint8_t v___x_619_; 
v___x_604_ = lean_st_ref_get(v___y_602_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
v_toConstantVal_606_ = lean_ctor_get(v_thm_601_, 0);
v_value_607_ = lean_ctor_get(v_thm_601_, 1);
v_all_608_ = lean_ctor_get(v_thm_601_, 2);
v_type_618_ = lean_ctor_get(v_toConstantVal_606_, 2);
lean_inc_ref(v_env_605_);
v___x_619_ = l_Lean_Environment_hasUnsafe(v_env_605_, v_type_618_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; 
v___x_620_ = l_Lean_Environment_hasUnsafe(v_env_605_, v_value_607_);
v___y_610_ = v___x_620_;
goto v___jp_609_;
}
else
{
lean_dec_ref(v_env_605_);
v___y_610_ = v___x_619_;
goto v___jp_609_;
}
v___jp_609_:
{
if (v___y_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_611_, 0, v_thm_601_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_inc(v_all_608_);
lean_inc_ref(v_value_607_);
lean_inc_ref(v_toConstantVal_606_);
lean_dec_ref(v_thm_601_);
v___x_613_ = lean_box(0);
v___x_614_ = 0;
v___x_615_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_615_, 0, v_toConstantVal_606_);
lean_ctor_set(v___x_615_, 1, v_value_607_);
lean_ctor_set(v___x_615_, 2, v___x_613_);
lean_ctor_set(v___x_615_, 3, v_all_608_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*4, v___x_614_);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_621_, v___y_622_);
lean_dec(v___y_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_625_, v___y_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_639_, lean_object* v_b_640_, lean_object* v_c_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_apply_7(v_k_639_, v_b_640_, v_c_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, lean_box(0));
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_648_, lean_object* v_b_649_, lean_object* v_c_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_648_, v_b_649_, v_c_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_657_, lean_object* v_k_658_, uint8_t v_cleanupAnnotations_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___f_665_; uint8_t v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___f_665_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_665_, 0, v_k_658_);
v___x_666_ = 1;
v___x_667_ = 0;
v___x_668_ = lean_box(0);
v___x_669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_657_, v___x_666_, v___x_667_, v___x_666_, v___x_667_, v___x_668_, v___f_665_, v_cleanupAnnotations_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_669_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_669_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_686_, lean_object* v_k_687_, lean_object* v_cleanupAnnotations_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_694_; lean_object* v_res_695_; 
v_cleanupAnnotations_boxed_694_ = lean_unbox(v_cleanupAnnotations_688_);
v_res_695_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_686_, v_k_687_, v_cleanupAnnotations_boxed_694_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_696_, lean_object* v_e_697_, lean_object* v_k_698_, uint8_t v_cleanupAnnotations_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_697_, v_k_698_, v_cleanupAnnotations_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_706_, lean_object* v_e_707_, lean_object* v_k_708_, lean_object* v_cleanupAnnotations_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_715_; lean_object* v_res_716_; 
v_cleanupAnnotations_boxed_715_ = lean_unbox(v_cleanupAnnotations_709_);
v_res_716_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_706_, v_e_707_, v_k_708_, v_cleanupAnnotations_boxed_715_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
if (lean_obj_tag(v_a_717_) == 0)
{
lean_object* v___x_719_; 
v___x_719_ = l_List_reverse___redArg(v_a_718_);
return v___x_719_;
}
else
{
lean_object* v_head_720_; lean_object* v_tail_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_730_; 
v_head_720_ = lean_ctor_get(v_a_717_, 0);
v_tail_721_ = lean_ctor_get(v_a_717_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_a_717_);
if (v_isSharedCheck_730_ == 0)
{
v___x_723_ = v_a_717_;
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_tail_721_);
lean_inc(v_head_720_);
lean_dec(v_a_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = l_Lean_mkLevelParam(v_head_720_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v_a_718_);
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_a_718_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v_a_717_ = v_tail_721_;
v_a_718_ = v___x_727_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_731_, lean_object* v_name_732_, lean_object* v_xs_733_, lean_object* v_body_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_name_740_; lean_object* v_levelParams_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_811_; 
v_name_740_ = lean_ctor_get(v_toConstantVal_731_, 0);
v_levelParams_741_ = lean_ctor_get(v_toConstantVal_731_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_toConstantVal_731_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v_toConstantVal_731_, 2);
lean_dec(v_unused_812_);
v___x_743_ = v_toConstantVal_731_;
v_isShared_744_ = v_isSharedCheck_811_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_levelParams_741_);
lean_inc(v_name_740_);
lean_dec(v_toConstantVal_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_811_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_lhs_748_; lean_object* v___x_749_; 
v___x_745_ = lean_box(0);
lean_inc(v_levelParams_741_);
v___x_746_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_741_, v___x_745_);
v___x_747_ = l_Lean_mkConst(v_name_740_, v___x_746_);
v_lhs_748_ = l_Lean_mkAppN(v___x_747_, v_xs_733_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc_ref(v_lhs_748_);
v___x_749_ = l_Lean_Meta_mkEq(v_lhs_748_, v_body_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; uint8_t v___x_751_; uint8_t v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref(v___x_749_);
v___x_751_ = 0;
v___x_752_ = 1;
v___x_753_ = 1;
v___x_754_ = l_Lean_Meta_mkForallFVars(v_xs_733_, v_a_750_, v___x_751_, v___x_752_, v___x_752_, v___x_753_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref(v___x_754_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
v___x_756_ = l_Lean_Meta_letToHave(v_a_755_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref(v___x_756_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
v___x_758_ = l_Lean_Meta_mkEqRefl(v_lhs_748_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v___x_758_);
v___x_760_ = l_Lean_Meta_mkLambdaFVars(v_xs_733_, v_a_759_, v___x_751_, v___x_752_, v___x_751_, v___x_752_, v___x_753_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref(v___x_760_);
lean_inc(v_name_732_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 2, v_a_757_);
lean_ctor_set(v___x_743_, 0, v_name_732_);
v___x_763_ = v___x_743_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_name_732_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_levelParams_741_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_a_757_);
v___x_763_ = v_reuseFailAlloc_770_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_a_767_; lean_object* v___x_768_; 
lean_inc(v_name_732_);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v_name_732_);
lean_ctor_set(v___x_764_, 1, v___x_745_);
v___x_765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v_a_761_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
v___x_766_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_765_, v___y_738_);
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
v___x_768_ = l_Lean_addDecl(v_a_767_, v___x_751_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; 
lean_dec_ref(v___x_768_);
v___x_769_ = l_Lean_inferDefEqAttr(v_name_732_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_769_;
}
else
{
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_name_732_);
return v___x_768_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_a_757_);
lean_del_object(v___x_743_);
lean_dec(v_levelParams_741_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_name_732_);
v_a_771_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_760_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_760_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_a_757_);
lean_del_object(v___x_743_);
lean_dec(v_levelParams_741_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_name_732_);
v_a_779_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_758_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_758_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_lhs_748_);
lean_del_object(v___x_743_);
lean_dec(v_levelParams_741_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_name_732_);
v_a_787_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_756_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_756_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_lhs_748_);
lean_del_object(v___x_743_);
lean_dec(v_levelParams_741_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_name_732_);
v_a_795_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_754_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_754_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v_lhs_748_);
lean_del_object(v___x_743_);
lean_dec(v_levelParams_741_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_name_732_);
v_a_803_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_749_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_749_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_813_, lean_object* v_name_814_, lean_object* v_xs_815_, lean_object* v_body_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_813_, v_name_814_, v_xs_815_, v_body_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec_ref(v_xs_815_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_823_, lean_object* v_info_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_toConstantVal_830_; lean_object* v_value_831_; lean_object* v___f_832_; uint8_t v___x_833_; lean_object* v___x_834_; 
v_toConstantVal_830_ = lean_ctor_get(v_info_824_, 0);
lean_inc_ref(v_toConstantVal_830_);
v_value_831_ = lean_ctor_get(v_info_824_, 1);
lean_inc_ref(v_value_831_);
lean_dec_ref(v_info_824_);
v___f_832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_832_, 0, v_toConstantVal_830_);
lean_closure_set(v___f_832_, 1, v_name_823_);
v___x_833_ = 1;
v___x_834_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_831_, v___f_832_, v___x_833_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_835_, lean_object* v_info_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_835_, v_info_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_843_, lean_object* v_name_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_853_; lean_object* v_env_854_; uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_853_ = lean_st_ref_get(v_a_848_);
v_env_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc_ref(v_env_854_);
lean_dec(v___x_853_);
v___x_855_ = 0;
lean_inc(v_declName_843_);
v___x_856_ = l_Lean_Environment_find_x3f(v_env_854_, v_declName_843_, v___x_855_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v_val_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_883_; 
v_val_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_883_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_883_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_val_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_883_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
if (lean_obj_tag(v_val_857_) == 1)
{
lean_object* v_val_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_val_861_ = lean_ctor_get(v_val_857_, 0);
lean_inc_ref(v_val_861_);
lean_dec_ref(v_val_857_);
lean_inc(v_name_844_);
v___x_862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_862_, 0, v_name_844_);
lean_closure_set(v___x_862_, 1, v_val_861_);
lean_inc(v_name_844_);
v___x_863_ = l_Lean_Meta_realizeConst(v_declName_843_, v_name_844_, v___x_862_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_873_; 
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_874_);
v___x_865_ = v___x_863_;
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_863_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v_name_844_);
v___x_868_ = v___x_859_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_name_844_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_del_object(v___x_859_);
lean_dec(v_name_844_);
v_a_875_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_863_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_863_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_del_object(v___x_859_);
lean_dec(v_val_857_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_name_844_);
lean_dec(v_declName_843_);
goto v___jp_850_;
}
}
}
else
{
lean_dec(v___x_856_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_name_844_);
lean_dec(v_declName_843_);
goto v___jp_850_;
}
v___jp_850_:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_884_, lean_object* v_name_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Meta_mkSimpleEqThm(v_declName_884_, v_name_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_892_, lean_object* v_vals_893_, lean_object* v_i_894_, lean_object* v_k_895_){
_start:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_array_get_size(v_keys_892_);
v___x_897_ = lean_nat_dec_lt(v_i_894_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec(v_i_894_);
v___x_898_ = lean_box(0);
return v___x_898_;
}
else
{
lean_object* v_k_x27_899_; uint8_t v___x_900_; 
v_k_x27_899_ = lean_array_fget_borrowed(v_keys_892_, v_i_894_);
v___x_900_ = lean_name_eq(v_k_895_, v_k_x27_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_add(v_i_894_, v___x_901_);
lean_dec(v_i_894_);
v_i_894_ = v___x_902_;
goto _start;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_array_fget_borrowed(v_vals_893_, v_i_894_);
lean_dec(v_i_894_);
lean_inc(v___x_904_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_906_, lean_object* v_vals_907_, lean_object* v_i_908_, lean_object* v_k_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_906_, v_vals_907_, v_i_908_, v_k_909_);
lean_dec(v_k_909_);
lean_dec_ref(v_vals_907_);
lean_dec_ref(v_keys_906_);
return v_res_910_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_911_; size_t v___x_912_; size_t v___x_913_; 
v___x_911_ = ((size_t)5ULL);
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_shift_left(v___x_912_, v___x_911_);
return v___x_913_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; 
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_916_ = lean_usize_sub(v___x_915_, v___x_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_917_, size_t v_x_918_, lean_object* v_x_919_){
_start:
{
if (lean_obj_tag(v_x_917_) == 0)
{
lean_object* v_es_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_941_; 
v_es_920_ = lean_ctor_get(v_x_917_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v_x_917_);
if (v_isSharedCheck_941_ == 0)
{
v___x_922_ = v_x_917_;
v_isShared_923_ = v_isSharedCheck_941_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_es_920_);
lean_dec(v_x_917_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_941_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; lean_object* v_j_928_; lean_object* v___x_929_; 
v___x_924_ = lean_box(2);
v___x_925_ = ((size_t)5ULL);
v___x_926_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_927_ = lean_usize_land(v_x_918_, v___x_926_);
v_j_928_ = lean_usize_to_nat(v___x_927_);
v___x_929_ = lean_array_get(v___x_924_, v_es_920_, v_j_928_);
lean_dec(v_j_928_);
lean_dec_ref(v_es_920_);
switch(lean_obj_tag(v___x_929_))
{
case 0:
{
lean_object* v_key_930_; lean_object* v_val_931_; uint8_t v___x_932_; 
v_key_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_key_930_);
v_val_931_ = lean_ctor_get(v___x_929_, 1);
lean_inc(v_val_931_);
lean_dec_ref(v___x_929_);
v___x_932_ = lean_name_eq(v_x_919_, v_key_930_);
lean_dec(v_key_930_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec(v_val_931_);
lean_del_object(v___x_922_);
v___x_933_ = lean_box(0);
return v___x_933_;
}
else
{
lean_object* v___x_935_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
lean_ctor_set(v___x_922_, 0, v_val_931_);
v___x_935_ = v___x_922_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_val_931_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
case 1:
{
lean_object* v_node_937_; size_t v___x_938_; 
lean_del_object(v___x_922_);
v_node_937_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_node_937_);
lean_dec_ref(v___x_929_);
v___x_938_ = lean_usize_shift_right(v_x_918_, v___x_925_);
v_x_917_ = v_node_937_;
v_x_918_ = v___x_938_;
goto _start;
}
default: 
{
lean_object* v___x_940_; 
lean_del_object(v___x_922_);
v___x_940_ = lean_box(0);
return v___x_940_;
}
}
}
}
else
{
lean_object* v_ks_942_; lean_object* v_vs_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_ks_942_ = lean_ctor_get(v_x_917_, 0);
lean_inc_ref(v_ks_942_);
v_vs_943_ = lean_ctor_get(v_x_917_, 1);
lean_inc_ref(v_vs_943_);
lean_dec_ref(v_x_917_);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_942_, v_vs_943_, v___x_944_, v_x_919_);
lean_dec_ref(v_vs_943_);
lean_dec_ref(v_ks_942_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
size_t v_x_468__boxed_949_; lean_object* v_res_950_; 
v_x_468__boxed_949_ = lean_unbox_usize(v_x_947_);
lean_dec(v_x_947_);
v_res_950_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_946_, v_x_468__boxed_949_, v_x_948_);
lean_dec(v_x_948_);
return v_res_950_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_951_; uint64_t v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(1723u);
v___x_952_ = lean_uint64_of_nat(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
uint64_t v___y_956_; 
if (lean_obj_tag(v_x_954_) == 0)
{
uint64_t v___x_959_; 
v___x_959_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_956_ = v___x_959_;
goto v___jp_955_;
}
else
{
uint64_t v_hash_960_; 
v_hash_960_ = lean_ctor_get_uint64(v_x_954_, sizeof(void*)*2);
v___y_956_ = v_hash_960_;
goto v___jp_955_;
}
v___jp_955_:
{
size_t v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_uint64_to_usize(v___y_956_);
v___x_958_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_953_, v___x_957_, v_x_954_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_961_, v_x_962_);
lean_dec(v_x_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v_env_968_; lean_object* v___x_969_; lean_object* v_asyncMode_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_967_ = lean_st_ref_get(v_a_965_);
v_env_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc_ref(v_env_968_);
lean_dec(v___x_967_);
v___x_969_ = l_Lean_Meta_eqnsExt;
v_asyncMode_970_ = lean_ctor_get(v___x_969_, 2);
lean_inc(v_asyncMode_970_);
v___x_971_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_972_ = lean_box(0);
v___x_973_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_971_, v___x_969_, v_env_968_, v_asyncMode_970_, v___x_972_);
lean_dec(v_asyncMode_970_);
v___x_974_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_973_, v_thmName_964_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec(v_thmName_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_980_, v_a_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_thmName_985_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_994_, v_x_995_, v_x_996_);
lean_dec(v_x_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, size_t v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_999_, v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
size_t v_x_594__boxed_1007_; lean_object* v_res_1008_; 
v_x_594__boxed_1007_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_res_1008_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1003_, v_x_1004_, v_x_594__boxed_1007_, v_x_1006_);
lean_dec(v_x_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1009_, lean_object* v_keys_1010_, lean_object* v_vals_1011_, lean_object* v_heq_1012_, lean_object* v_i_1013_, lean_object* v_k_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1010_, v_vals_1011_, v_i_1013_, v_k_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1016_, lean_object* v_keys_1017_, lean_object* v_vals_1018_, lean_object* v_heq_1019_, lean_object* v_i_1020_, lean_object* v_k_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1016_, v_keys_1017_, v_vals_1018_, v_heq_1019_, v_i_1020_, v_k_1021_);
lean_dec(v_k_1021_);
lean_dec_ref(v_vals_1018_);
lean_dec_ref(v_keys_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = lean_array_get_size(v_keys_1023_);
v___x_1027_ = lean_nat_dec_lt(v_i_1024_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_dec(v_i_1024_);
return v___x_1027_;
}
else
{
lean_object* v_k_x27_1028_; uint8_t v___x_1029_; 
v_k_x27_1028_ = lean_array_fget_borrowed(v_keys_1023_, v_i_1024_);
v___x_1029_ = lean_name_eq(v_k_1025_, v_k_x27_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_nat_add(v_i_1024_, v___x_1030_);
lean_dec(v_i_1024_);
v_i_1024_ = v___x_1031_;
goto _start;
}
else
{
lean_dec(v_i_1024_);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1033_, lean_object* v_i_1034_, lean_object* v_k_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1033_, v_i_1034_, v_k_1035_);
lean_dec(v_k_1035_);
lean_dec_ref(v_keys_1033_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1038_, size_t v_x_1039_, lean_object* v_x_1040_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
lean_object* v_es_1041_; lean_object* v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; lean_object* v_j_1046_; lean_object* v___x_1047_; 
v_es_1041_ = lean_ctor_get(v_x_1038_, 0);
lean_inc_ref(v_es_1041_);
lean_dec_ref(v_x_1038_);
v___x_1042_ = lean_box(2);
v___x_1043_ = ((size_t)5ULL);
v___x_1044_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1045_ = lean_usize_land(v_x_1039_, v___x_1044_);
v_j_1046_ = lean_usize_to_nat(v___x_1045_);
v___x_1047_ = lean_array_get(v___x_1042_, v_es_1041_, v_j_1046_);
lean_dec(v_j_1046_);
lean_dec_ref(v_es_1041_);
switch(lean_obj_tag(v___x_1047_))
{
case 0:
{
lean_object* v_key_1048_; uint8_t v___x_1049_; 
v_key_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_key_1048_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = lean_name_eq(v_x_1040_, v_key_1048_);
lean_dec(v_key_1048_);
return v___x_1049_;
}
case 1:
{
lean_object* v_node_1050_; size_t v___x_1051_; 
v_node_1050_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_node_1050_);
lean_dec_ref(v___x_1047_);
v___x_1051_ = lean_usize_shift_right(v_x_1039_, v___x_1043_);
v_x_1038_ = v_node_1050_;
v_x_1039_ = v___x_1051_;
goto _start;
}
default: 
{
uint8_t v___x_1053_; 
v___x_1053_ = 0;
return v___x_1053_;
}
}
}
else
{
lean_object* v_ks_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_ks_1054_ = lean_ctor_get(v_x_1038_, 0);
lean_inc_ref(v_ks_1054_);
lean_dec_ref(v_x_1038_);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1054_, v___x_1055_, v_x_1040_);
lean_dec_ref(v_ks_1054_);
return v___x_1056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
size_t v_x_448__boxed_1060_; uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_x_448__boxed_1060_ = lean_unbox_usize(v_x_1058_);
lean_dec(v_x_1058_);
v_res_1061_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1057_, v_x_448__boxed_1060_, v_x_1059_);
lean_dec(v_x_1059_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
uint64_t v___y_1066_; 
if (lean_obj_tag(v_x_1064_) == 0)
{
uint64_t v___x_1069_; 
v___x_1069_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1066_ = v___x_1069_;
goto v___jp_1065_;
}
else
{
uint64_t v_hash_1070_; 
v_hash_1070_ = lean_ctor_get_uint64(v_x_1064_, sizeof(void*)*2);
v___y_1066_ = v_hash_1070_;
goto v___jp_1065_;
}
v___jp_1065_:
{
size_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_uint64_to_usize(v___y_1066_);
v___x_1068_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1063_, v___x_1067_, v_x_1064_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1071_, v_x_1072_);
lean_dec(v_x_1072_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v_env_1079_; lean_object* v___x_1080_; lean_object* v_asyncMode_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1078_ = lean_st_ref_get(v_a_1076_);
v_env_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc_ref(v_env_1079_);
lean_dec(v___x_1078_);
v___x_1080_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1081_ = lean_ctor_get(v___x_1080_, 2);
lean_inc(v_asyncMode_1081_);
v___x_1082_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1083_ = lean_box(0);
v___x_1084_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1082_, v___x_1080_, v_env_1079_, v_asyncMode_1081_, v___x_1083_);
lean_dec(v_asyncMode_1081_);
v___x_1085_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1084_, v_thmName_1075_);
v___x_1086_ = lean_box(v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec(v_thmName_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1092_, v_a_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Meta_isEqnThm(v_thmName_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_thmName_1097_);
return v_res_1101_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1103_, v_x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1106_, v_x_1107_, v_x_1108_);
lean_dec(v_x_1108_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1111_, lean_object* v_x_1112_, size_t v_x_1113_, lean_object* v_x_1114_){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1112_, v_x_1113_, v_x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
size_t v_x_551__boxed_1120_; uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_x_551__boxed_1120_ = lean_unbox_usize(v_x_1118_);
lean_dec(v_x_1118_);
v_res_1121_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1116_, v_x_1117_, v_x_551__boxed_1120_, v_x_1119_);
lean_dec(v_x_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1123_, lean_object* v_keys_1124_, lean_object* v_vals_1125_, lean_object* v_heq_1126_, lean_object* v_i_1127_, lean_object* v_k_1128_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1124_, v_i_1127_, v_k_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1130_, lean_object* v_keys_1131_, lean_object* v_vals_1132_, lean_object* v_heq_1133_, lean_object* v_i_1134_, lean_object* v_k_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1130_, v_keys_1131_, v_vals_1132_, v_heq_1133_, v_i_1134_, v_k_1135_);
lean_dec(v_k_1135_);
lean_dec_ref(v_vals_1132_);
lean_dec_ref(v_keys_1131_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v_ks_1142_; lean_object* v_vs_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1167_; 
v_ks_1142_ = lean_ctor_get(v_x_1138_, 0);
v_vs_1143_ = lean_ctor_get(v_x_1138_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1138_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1145_ = v_x_1138_;
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_vs_1143_);
lean_inc(v_ks_1142_);
lean_dec(v_x_1138_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_array_get_size(v_ks_1142_);
v___x_1148_ = lean_nat_dec_lt(v_x_1139_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec(v_x_1139_);
v___x_1149_ = lean_array_push(v_ks_1142_, v_x_1140_);
v___x_1150_ = lean_array_push(v_vs_1143_, v_x_1141_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1150_);
lean_ctor_set(v___x_1145_, 0, v___x_1149_);
v___x_1152_ = v___x_1145_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v_k_x27_1154_; uint8_t v___x_1155_; 
v_k_x27_1154_ = lean_array_fget_borrowed(v_ks_1142_, v_x_1139_);
v___x_1155_ = lean_name_eq(v_x_1140_, v_k_x27_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1157_; 
if (v_isShared_1146_ == 0)
{
v___x_1157_ = v___x_1145_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_ks_1142_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_vs_1143_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_x_1139_, v___x_1158_);
lean_dec(v_x_1139_);
v_x_1138_ = v___x_1157_;
v_x_1139_ = v___x_1159_;
goto _start;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1162_ = lean_array_fset(v_ks_1142_, v_x_1139_, v_x_1140_);
v___x_1163_ = lean_array_fset(v_vs_1143_, v_x_1139_, v_x_1141_);
lean_dec(v_x_1139_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1163_);
lean_ctor_set(v___x_1145_, 0, v___x_1162_);
v___x_1165_ = v___x_1145_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1168_, lean_object* v_k_1169_, lean_object* v_v_1170_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1168_, v___x_1171_, v_k_1169_, v_v_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1174_, size_t v_x_1175_, size_t v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v_es_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v_j_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_es_1179_ = lean_ctor_get(v_x_1174_, 0);
v___x_1180_ = ((size_t)5ULL);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1183_ = lean_usize_land(v_x_1175_, v___x_1182_);
v_j_1184_ = lean_usize_to_nat(v___x_1183_);
v___x_1185_ = lean_array_get_size(v_es_1179_);
v___x_1186_ = lean_nat_dec_lt(v_j_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec(v_j_1184_);
lean_dec(v_x_1178_);
lean_dec(v_x_1177_);
return v_x_1174_;
}
else
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1223_; 
lean_inc_ref(v_es_1179_);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_x_1174_, 0);
lean_dec(v_unused_1224_);
v___x_1188_ = v_x_1174_;
v_isShared_1189_ = v_isSharedCheck_1223_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_x_1174_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1223_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_v_1190_; lean_object* v___x_1191_; lean_object* v_xs_x27_1192_; lean_object* v___y_1194_; 
v_v_1190_ = lean_array_fget(v_es_1179_, v_j_1184_);
v___x_1191_ = lean_box(0);
v_xs_x27_1192_ = lean_array_fset(v_es_1179_, v_j_1184_, v___x_1191_);
switch(lean_obj_tag(v_v_1190_))
{
case 0:
{
lean_object* v_key_1199_; lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1210_; 
v_key_1199_ = lean_ctor_get(v_v_1190_, 0);
v_val_1200_ = lean_ctor_get(v_v_1190_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_v_1190_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1202_ = v_v_1190_;
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_inc(v_key_1199_);
lean_dec(v_v_1190_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_name_eq(v_x_1177_, v_key_1199_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_del_object(v___x_1202_);
v___x_1205_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1199_, v_val_1200_, v_x_1177_, v_x_1178_);
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
v___y_1194_ = v___x_1206_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1208_; 
lean_dec(v_val_1200_);
lean_dec(v_key_1199_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v_x_1178_);
lean_ctor_set(v___x_1202_, 0, v_x_1177_);
v___x_1208_ = v___x_1202_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_x_1177_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_x_1178_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
v___y_1194_ = v___x_1208_;
goto v___jp_1193_;
}
}
}
}
case 1:
{
lean_object* v_node_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1221_; 
v_node_1211_ = lean_ctor_get(v_v_1190_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_v_1190_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1213_ = v_v_1190_;
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_node_1211_);
lean_dec(v_v_1190_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1215_ = lean_usize_shift_right(v_x_1175_, v___x_1180_);
v___x_1216_ = lean_usize_add(v_x_1176_, v___x_1181_);
v___x_1217_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1211_, v___x_1215_, v___x_1216_, v_x_1177_, v_x_1178_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1217_);
v___x_1219_ = v___x_1213_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v___y_1194_ = v___x_1219_;
goto v___jp_1193_;
}
}
}
default: 
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_x_1177_);
lean_ctor_set(v___x_1222_, 1, v_x_1178_);
v___y_1194_ = v___x_1222_;
goto v___jp_1193_;
}
}
v___jp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_array_fset(v_xs_x27_1192_, v_j_1184_, v___y_1194_);
lean_dec(v_j_1184_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1195_);
v___x_1197_ = v___x_1188_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
else
{
lean_object* v_ks_1225_; lean_object* v_vs_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1246_; 
v_ks_1225_ = lean_ctor_get(v_x_1174_, 0);
v_vs_1226_ = lean_ctor_get(v_x_1174_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1228_ = v_x_1174_;
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_vs_1226_);
lean_inc(v_ks_1225_);
lean_dec(v_x_1174_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_ks_1225_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_vs_1226_);
v___x_1231_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v_newNode_1232_; uint8_t v___y_1234_; size_t v___x_1240_; uint8_t v___x_1241_; 
v_newNode_1232_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1231_, v_x_1177_, v_x_1178_);
v___x_1240_ = ((size_t)7ULL);
v___x_1241_ = lean_usize_dec_le(v___x_1240_, v_x_1176_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1242_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1232_);
v___x_1243_ = lean_unsigned_to_nat(4u);
v___x_1244_ = lean_nat_dec_lt(v___x_1242_, v___x_1243_);
lean_dec(v___x_1242_);
v___y_1234_ = v___x_1244_;
goto v___jp_1233_;
}
else
{
v___y_1234_ = v___x_1241_;
goto v___jp_1233_;
}
v___jp_1233_:
{
if (v___y_1234_ == 0)
{
lean_object* v_ks_1235_; lean_object* v_vs_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_ks_1235_ = lean_ctor_get(v_newNode_1232_, 0);
lean_inc_ref(v_ks_1235_);
v_vs_1236_ = lean_ctor_get(v_newNode_1232_, 1);
lean_inc_ref(v_vs_1236_);
lean_dec_ref(v_newNode_1232_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1176_, v_ks_1235_, v_vs_1236_, v___x_1237_, v___x_1238_);
lean_dec_ref(v_vs_1236_);
lean_dec_ref(v_ks_1235_);
return v___x_1239_;
}
else
{
return v_newNode_1232_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1247_, lean_object* v_keys_1248_, lean_object* v_vals_1249_, lean_object* v_i_1250_, lean_object* v_entries_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_array_get_size(v_keys_1248_);
v___x_1253_ = lean_nat_dec_lt(v_i_1250_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec(v_i_1250_);
return v_entries_1251_;
}
else
{
lean_object* v_k_1254_; lean_object* v_v_1255_; uint64_t v___y_1257_; 
v_k_1254_ = lean_array_fget_borrowed(v_keys_1248_, v_i_1250_);
v_v_1255_ = lean_array_fget_borrowed(v_vals_1249_, v_i_1250_);
if (lean_obj_tag(v_k_1254_) == 0)
{
uint64_t v___x_1268_; 
v___x_1268_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1257_ = v___x_1268_;
goto v___jp_1256_;
}
else
{
uint64_t v_hash_1269_; 
v_hash_1269_ = lean_ctor_get_uint64(v_k_1254_, sizeof(void*)*2);
v___y_1257_ = v_hash_1269_;
goto v___jp_1256_;
}
v___jp_1256_:
{
size_t v_h_1258_; size_t v___x_1259_; lean_object* v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v_h_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_h_1258_ = lean_uint64_to_usize(v___y_1257_);
v___x_1259_ = ((size_t)5ULL);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_sub(v_depth_1247_, v___x_1261_);
v___x_1263_ = lean_usize_mul(v___x_1259_, v___x_1262_);
v_h_1264_ = lean_usize_shift_right(v_h_1258_, v___x_1263_);
v___x_1265_ = lean_nat_add(v_i_1250_, v___x_1260_);
lean_dec(v_i_1250_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
v___x_1266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1251_, v_h_1264_, v_depth_1247_, v_k_1254_, v_v_1255_);
v_i_1250_ = v___x_1265_;
v_entries_1251_ = v___x_1266_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1270_, lean_object* v_keys_1271_, lean_object* v_vals_1272_, lean_object* v_i_1273_, lean_object* v_entries_1274_){
_start:
{
size_t v_depth_boxed_1275_; lean_object* v_res_1276_; 
v_depth_boxed_1275_ = lean_unbox_usize(v_depth_1270_);
lean_dec(v_depth_1270_);
v_res_1276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1275_, v_keys_1271_, v_vals_1272_, v_i_1273_, v_entries_1274_);
lean_dec_ref(v_vals_1272_);
lean_dec_ref(v_keys_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
size_t v_x_638__boxed_1282_; size_t v_x_639__boxed_1283_; lean_object* v_res_1284_; 
v_x_638__boxed_1282_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_x_639__boxed_1283_ = lean_unbox_usize(v_x_1279_);
lean_dec(v_x_1279_);
v_res_1284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1277_, v_x_638__boxed_1282_, v_x_639__boxed_1283_, v_x_1280_, v_x_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_){
_start:
{
uint64_t v___y_1289_; 
if (lean_obj_tag(v_x_1286_) == 0)
{
uint64_t v___x_1293_; 
v___x_1293_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1289_ = v___x_1293_;
goto v___jp_1288_;
}
else
{
uint64_t v_hash_1294_; 
v_hash_1294_ = lean_ctor_get_uint64(v_x_1286_, sizeof(void*)*2);
v___y_1289_ = v_hash_1294_;
goto v___jp_1288_;
}
v___jp_1288_:
{
size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_uint64_to_usize(v___y_1289_);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1285_, v___x_1290_, v___x_1291_, v_x_1286_, v_x_1287_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1295_, lean_object* v_as_1296_, size_t v_i_1297_, size_t v_stop_1298_, lean_object* v_b_1299_){
_start:
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_usize_dec_eq(v_i_1297_, v_stop_1298_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; 
v___x_1301_ = lean_array_uget_borrowed(v_as_1296_, v_i_1297_);
lean_inc(v_declName_1295_);
lean_inc(v___x_1301_);
v___x_1302_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1299_, v___x_1301_, v_declName_1295_);
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_add(v_i_1297_, v___x_1303_);
v_i_1297_ = v___x_1304_;
v_b_1299_ = v___x_1302_;
goto _start;
}
else
{
lean_dec(v_declName_1295_);
return v_b_1299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1306_, lean_object* v_as_1307_, lean_object* v_i_1308_, lean_object* v_stop_1309_, lean_object* v_b_1310_){
_start:
{
size_t v_i_boxed_1311_; size_t v_stop_boxed_1312_; lean_object* v_res_1313_; 
v_i_boxed_1311_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_stop_boxed_1312_ = lean_unbox_usize(v_stop_1309_);
lean_dec(v_stop_1309_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1306_, v_as_1307_, v_i_boxed_1311_, v_stop_boxed_1312_, v_b_1310_);
lean_dec_ref(v_as_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1314_, lean_object* v_declName_1315_, lean_object* v_s_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_get_size(v_eqThms_1314_);
v___x_1319_ = lean_nat_dec_lt(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec(v_declName_1315_);
return v_s_1316_;
}
else
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_nat_dec_le(v___x_1318_, v___x_1318_);
if (v___x_1320_ == 0)
{
if (v___x_1319_ == 0)
{
lean_dec(v_declName_1315_);
return v_s_1316_;
}
else
{
size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = lean_usize_of_nat(v___x_1318_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1315_, v_eqThms_1314_, v___x_1321_, v___x_1322_, v_s_1316_);
return v___x_1323_;
}
}
else
{
size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = lean_usize_of_nat(v___x_1318_);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1315_, v_eqThms_1314_, v___x_1324_, v___x_1325_, v_s_1316_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1327_, lean_object* v_declName_1328_, lean_object* v_s_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1327_, v_declName_1328_, v_s_1329_);
lean_dec_ref(v_eqThms_1327_);
return v_res_1330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0(void){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1336_, lean_object* v_eqThms_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1340_; lean_object* v_env_1341_; lean_object* v_nextMacroScope_1342_; lean_object* v_ngen_1343_; lean_object* v_auxDeclNGen_1344_; lean_object* v_traceState_1345_; lean_object* v_messages_1346_; lean_object* v_infoState_1347_; lean_object* v_snapshotTasks_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1364_; 
v___x_1340_ = lean_st_ref_take(v_a_1338_);
v_env_1341_ = lean_ctor_get(v___x_1340_, 0);
v_nextMacroScope_1342_ = lean_ctor_get(v___x_1340_, 1);
v_ngen_1343_ = lean_ctor_get(v___x_1340_, 2);
v_auxDeclNGen_1344_ = lean_ctor_get(v___x_1340_, 3);
v_traceState_1345_ = lean_ctor_get(v___x_1340_, 4);
v_messages_1346_ = lean_ctor_get(v___x_1340_, 6);
v_infoState_1347_ = lean_ctor_get(v___x_1340_, 7);
v_snapshotTasks_1348_ = lean_ctor_get(v___x_1340_, 8);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v___x_1340_, 5);
lean_dec(v_unused_1365_);
v___x_1350_ = v___x_1340_;
v_isShared_1351_ = v_isSharedCheck_1364_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_snapshotTasks_1348_);
lean_inc(v_infoState_1347_);
lean_inc(v_messages_1346_);
lean_inc(v_traceState_1345_);
lean_inc(v_auxDeclNGen_1344_);
lean_inc(v_ngen_1343_);
lean_inc(v_nextMacroScope_1342_);
lean_inc(v_env_1341_);
lean_dec(v___x_1340_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1364_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v_asyncMode_1353_; lean_object* v___f_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1352_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1353_ = lean_ctor_get(v___x_1352_, 2);
lean_inc(v_asyncMode_1353_);
v___f_1354_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1354_, 0, v_eqThms_1337_);
lean_closure_set(v___f_1354_, 1, v_declName_1336_);
v___x_1355_ = lean_box(0);
v___x_1356_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1352_, v_env_1341_, v___f_1354_, v_asyncMode_1353_, v___x_1355_);
lean_dec(v_asyncMode_1353_);
v___x_1357_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 5, v___x_1357_);
lean_ctor_set(v___x_1350_, 0, v___x_1356_);
v___x_1359_ = v___x_1350_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_nextMacroScope_1342_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_ngen_1343_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_auxDeclNGen_1344_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_traceState_1345_);
lean_ctor_set(v_reuseFailAlloc_1363_, 5, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1363_, 6, v_messages_1346_);
lean_ctor_set(v_reuseFailAlloc_1363_, 7, v_infoState_1347_);
lean_ctor_set(v_reuseFailAlloc_1363_, 8, v_snapshotTasks_1348_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_st_ref_set(v_a_1338_, v___x_1359_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1366_, lean_object* v_eqThms_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1366_, v_eqThms_1367_, v_a_1368_);
lean_dec(v_a_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1371_, lean_object* v_eqThms_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1371_, v_eqThms_1372_, v_a_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1377_, lean_object* v_eqThms_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1377_, v_eqThms_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1384_, v_x_1385_, v_x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1388_, lean_object* v_x_1389_, size_t v_x_1390_, size_t v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1389_, v_x_1390_, v_x_1391_, v_x_1392_, v_x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
size_t v_x_925__boxed_1401_; size_t v_x_926__boxed_1402_; lean_object* v_res_1403_; 
v_x_925__boxed_1401_ = lean_unbox_usize(v_x_1397_);
lean_dec(v_x_1397_);
v_x_926__boxed_1402_ = lean_unbox_usize(v_x_1398_);
lean_dec(v_x_1398_);
v_res_1403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1395_, v_x_1396_, v_x_925__boxed_1401_, v_x_926__boxed_1402_, v_x_1399_, v_x_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1404_, lean_object* v_n_1405_, lean_object* v_k_1406_, lean_object* v_v_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1405_, v_k_1406_, v_v_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1409_, size_t v_depth_1410_, lean_object* v_keys_1411_, lean_object* v_vals_1412_, lean_object* v_heq_1413_, lean_object* v_i_1414_, lean_object* v_entries_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1410_, v_keys_1411_, v_vals_1412_, v_i_1414_, v_entries_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1417_, lean_object* v_depth_1418_, lean_object* v_keys_1419_, lean_object* v_vals_1420_, lean_object* v_heq_1421_, lean_object* v_i_1422_, lean_object* v_entries_1423_){
_start:
{
size_t v_depth_boxed_1424_; lean_object* v_res_1425_; 
v_depth_boxed_1424_ = lean_unbox_usize(v_depth_1418_);
lean_dec(v_depth_1418_);
v_res_1425_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1417_, v_depth_boxed_1424_, v_keys_1419_, v_vals_1420_, v_heq_1421_, v_i_1422_, v_entries_1423_);
lean_dec_ref(v_vals_1420_);
lean_dec_ref(v_keys_1419_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1427_, v_x_1428_, v_x_1429_, v_x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1432_, lean_object* v_env_1433_, lean_object* v_idx_1434_, lean_object* v_eqs_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v_nextEq_1442_; uint8_t v___x_1443_; 
v___x_1437_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_nat_add(v_idx_1434_, v___x_1438_);
lean_dec(v_idx_1434_);
lean_inc(v___x_1439_);
v___x_1440_ = l_Nat_reprFast(v___x_1439_);
v___x_1441_ = lean_string_append(v___x_1437_, v___x_1440_);
lean_dec_ref(v___x_1440_);
lean_inc(v_declName_1432_);
lean_inc_ref(v_env_1433_);
v_nextEq_1442_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1433_, v_declName_1432_, v___x_1441_);
lean_inc_ref(v_env_1433_);
v___x_1443_ = l_Lean_Environment_containsOnBranch(v_env_1433_, v_nextEq_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_dec(v_nextEq_1442_);
lean_dec(v___x_1439_);
lean_dec_ref(v_env_1433_);
lean_dec(v_declName_1432_);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_eqs_1435_);
return v___x_1444_;
}
else
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_array_push(v_eqs_1435_, v_nextEq_1442_);
v_idx_1434_ = v___x_1439_;
v_eqs_1435_ = v___x_1445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1447_, lean_object* v_env_1448_, lean_object* v_idx_1449_, lean_object* v_eqs_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1447_, v_env_1448_, v_idx_1449_, v_eqs_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1453_, lean_object* v_env_1454_, lean_object* v_idx_1455_, lean_object* v_eqs_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1453_, v_env_1454_, v_idx_1455_, v_eqs_1456_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1463_, lean_object* v_env_1464_, lean_object* v_idx_1465_, lean_object* v_eqs_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1463_, v_env_1464_, v_idx_1465_, v_eqs_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v_env_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1476_ = lean_st_ref_get(v_a_1474_);
v_env_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_ref(v_env_1477_);
lean_dec(v___x_1476_);
v___x_1478_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1473_);
lean_inc_ref(v_env_1477_);
v___x_1479_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1477_, v_declName_1473_, v___x_1478_);
v___x_1480_ = 1;
lean_inc(v___x_1479_);
lean_inc_ref(v_env_1477_);
v___x_1481_ = l_Lean_Environment_contains(v_env_1477_, v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v___x_1479_);
lean_dec_ref(v_env_1477_);
lean_dec(v_declName_1473_);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1484_);
v___x_1486_ = lean_array_push(v___x_1485_, v___x_1479_);
lean_inc(v_declName_1473_);
v___x_1487_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1473_, v_env_1477_, v___x_1484_, v___x_1486_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1497_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
lean_inc(v_a_1488_);
v___x_1489_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1473_, v_a_1488_, v_a_1474_);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v___x_1489_, 0);
lean_dec(v_unused_1498_);
v___x_1491_ = v___x_1489_;
v_isShared_1492_ = v_isSharedCheck_1497_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v___x_1489_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1497_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_a_1488_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1493_);
v___x_1495_ = v___x_1491_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_declName_1473_);
v_a_1499_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1487_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1487_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1507_, v_a_1508_);
lean_dec(v_a_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1511_, v_a_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1525_, lean_object* v_localInsts_1526_, lean_object* v_x_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1525_, v_localInsts_1526_, v_x_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
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
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1533_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1533_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1550_, lean_object* v_localInsts_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1550_, v_localInsts_1551_, v_x_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1559_, lean_object* v_lctx_1560_, lean_object* v_localInsts_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1560_, v_localInsts_1561_, v_x_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1569_, lean_object* v_lctx_1570_, lean_object* v_localInsts_1571_, lean_object* v_x_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1569_, v_lctx_1570_, v_localInsts_1571_, v_x_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1582_, lean_object* v_as_x27_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
if (lean_obj_tag(v_as_x27_1583_) == 0)
{
lean_object* v___x_1590_; 
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v_declName_1582_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_b_1584_);
return v___x_1590_;
}
else
{
lean_object* v_head_1591_; lean_object* v_tail_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v_b_1584_);
v_head_1591_ = lean_ctor_get(v_as_x27_1583_, 0);
v_tail_1592_ = lean_ctor_get(v_as_x27_1583_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_as_x27_1583_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1594_ = v_as_x27_1583_;
v_isShared_1595_ = v_isSharedCheck_1623_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_tail_1592_);
lean_inc(v_head_1591_);
lean_dec(v_as_x27_1583_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1623_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; 
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc(v_declName_1582_);
v___x_1596_ = lean_apply_6(v_head_1591_, v_declName_1582_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, lean_box(0));
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1598_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = lean_box(0);
if (lean_obj_tag(v_a_1597_) == 1)
{
lean_object* v_val_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_tail_1592_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
v_val_1599_ = lean_ctor_get(v_a_1597_, 0);
lean_inc(v_val_1599_);
v___x_1600_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1582_, v_val_1599_, v___y_1588_);
lean_dec(v___y_1588_);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v___x_1600_, 0);
lean_dec(v_unused_1612_);
v___x_1602_ = v___x_1600_;
v_isShared_1603_ = v_isSharedCheck_1611_;
goto v_resetjp_1601_;
}
else
{
lean_dec(v___x_1600_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1611_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_a_1597_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 0);
lean_ctor_set(v___x_1594_, 1, v___x_1598_);
lean_ctor_set(v___x_1594_, 0, v___x_1604_);
v___x_1606_ = v___x_1594_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1598_);
v___x_1606_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1606_);
v___x_1608_ = v___x_1602_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
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
else
{
lean_object* v___x_1613_; 
lean_dec(v_a_1597_);
lean_del_object(v___x_1594_);
v___x_1613_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1583_ = v_tail_1592_;
v_b_1584_ = v___x_1613_;
goto _start;
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_del_object(v___x_1594_);
lean_dec(v_tail_1592_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v_declName_1582_);
v_a_1615_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1596_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1596_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1624_, lean_object* v_as_x27_1625_, lean_object* v_b_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1624_, v_as_x27_1625_, v_b_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
lean_inc(v___y_1637_);
lean_inc_ref(v___y_1636_);
lean_inc(v___y_1635_);
lean_inc_ref(v___y_1634_);
lean_inc(v_declName_1633_);
v___x_1639_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1677_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1677_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1677_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_unbox(v_a_1640_);
lean_dec(v_a_1640_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_declName_1633_);
v___x_1645_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1645_);
v___x_1647_ = v___x_1642_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
else
{
lean_object* v___x_1649_; 
lean_del_object(v___x_1642_);
lean_inc(v_declName_1633_);
v___x_1649_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1633_, v___y_1637_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
if (lean_obj_tag(v_a_1650_) == 1)
{
lean_dec_ref(v_a_1650_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_declName_1633_);
return v___x_1649_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec_ref(v___x_1649_);
lean_dec(v_a_1650_);
v___x_1651_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1652_ = lean_st_ref_get(v___x_1651_);
v___x_1653_ = lean_box(0);
v___x_1654_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1655_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1633_, v___x_1652_, v___x_1654_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1668_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1668_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1668_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_fst_1660_; 
v_fst_1660_ = lean_ctor_get(v_a_1656_, 0);
lean_inc(v_fst_1660_);
lean_dec(v_a_1656_);
if (lean_obj_tag(v_fst_1660_) == 0)
{
lean_object* v___x_1662_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1653_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1653_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
else
{
lean_object* v_val_1664_; lean_object* v___x_1666_; 
v_val_1664_ = lean_ctor_get(v_fst_1660_, 0);
lean_inc(v_val_1664_);
lean_dec_ref(v_fst_1660_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_val_1664_);
v___x_1666_ = v___x_1658_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_val_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1655_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1655_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_declName_1633_);
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_declName_1633_);
v_a_1678_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1639_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1639_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v_res_1692_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_box(1);
v___x_1697_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___x_1697_);
lean_ctor_set(v___x_1699_, 2, v___x_1696_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___f_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___f_1708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1708_, 0, v_declName_1702_);
v___x_1709_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1710_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1711_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1709_, v___x_1710_, v___f_1708_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1719_, lean_object* v_as_1720_, lean_object* v_as_x27_1721_, lean_object* v_b_1722_, lean_object* v_a_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1719_, v_as_x27_1721_, v_b_1722_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1730_, lean_object* v_as_1731_, lean_object* v_as_x27_1732_, lean_object* v_b_1733_, lean_object* v_a_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1730_, v_as_1731_, v_as_x27_1732_, v_b_1733_, v_a_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v_as_1731_);
return v_res_1740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(lean_object* v_opts_1741_, lean_object* v_opt_1742_){
_start:
{
lean_object* v_name_1743_; lean_object* v_defValue_1744_; lean_object* v_map_1745_; lean_object* v___x_1746_; 
v_name_1743_ = lean_ctor_get(v_opt_1742_, 0);
v_defValue_1744_ = lean_ctor_get(v_opt_1742_, 1);
v_map_1745_ = lean_ctor_get(v_opts_1741_, 0);
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1745_, v_name_1743_);
if (lean_obj_tag(v___x_1746_) == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_unbox(v_defValue_1744_);
return v___x_1747_;
}
else
{
lean_object* v_val_1748_; 
v_val_1748_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_val_1748_);
lean_dec_ref(v___x_1746_);
if (lean_obj_tag(v_val_1748_) == 1)
{
uint8_t v_v_1749_; 
v_v_1749_ = lean_ctor_get_uint8(v_val_1748_, 0);
lean_dec_ref(v_val_1748_);
return v_v_1749_;
}
else
{
uint8_t v___x_1750_; 
lean_dec(v_val_1748_);
v___x_1750_ = lean_unbox(v_defValue_1744_);
return v___x_1750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1___boxed(lean_object* v_opts_1751_, lean_object* v_opt_1752_){
_start:
{
uint8_t v_res_1753_; lean_object* v_r_1754_; 
v_res_1753_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_1751_, v_opt_1752_);
lean_dec_ref(v_opt_1752_);
lean_dec_ref(v_opts_1751_);
v_r_1754_ = lean_box(v_res_1753_);
return v_r_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(lean_object* v_opts_1755_, lean_object* v_opt_1756_){
_start:
{
lean_object* v_name_1757_; lean_object* v_defValue_1758_; lean_object* v_map_1759_; lean_object* v___x_1760_; 
v_name_1757_ = lean_ctor_get(v_opt_1756_, 0);
v_defValue_1758_ = lean_ctor_get(v_opt_1756_, 1);
v_map_1759_ = lean_ctor_get(v_opts_1755_, 0);
v___x_1760_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1759_, v_name_1757_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_inc(v_defValue_1758_);
return v_defValue_1758_;
}
else
{
lean_object* v_val_1761_; 
v_val_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_val_1761_);
lean_dec_ref(v___x_1760_);
if (lean_obj_tag(v_val_1761_) == 3)
{
lean_object* v_v_1762_; 
v_v_1762_ = lean_ctor_get(v_val_1761_, 0);
lean_inc(v_v_1762_);
lean_dec_ref(v_val_1761_);
return v_v_1762_;
}
else
{
lean_dec(v_val_1761_);
lean_inc(v_defValue_1758_);
return v_defValue_1758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2___boxed(lean_object* v_opts_1763_, lean_object* v_opt_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_1763_, v_opt_1764_);
lean_dec_ref(v_opt_1764_);
lean_dec_ref(v_opts_1763_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(lean_object* v_o_1769_, lean_object* v_k_1770_, uint8_t v_v_1771_){
_start:
{
lean_object* v_map_1772_; uint8_t v_hasTrace_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1787_; 
v_map_1772_ = lean_ctor_get(v_o_1769_, 0);
v_hasTrace_1773_ = lean_ctor_get_uint8(v_o_1769_, sizeof(void*)*1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_o_1769_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1775_ = v_o_1769_;
v_isShared_1776_ = v_isSharedCheck_1787_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_map_1772_);
lean_dec(v_o_1769_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1787_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1777_, 0, v_v_1771_);
lean_inc(v_k_1770_);
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1770_, v___x_1777_, v_map_1772_);
if (v_hasTrace_1773_ == 0)
{
lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1782_; 
v___x_1779_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1780_ = l_Lean_Name_isPrefixOf(v___x_1779_, v_k_1770_);
lean_dec(v_k_1770_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1778_);
v___x_1782_ = v___x_1775_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1778_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*1, v___x_1780_);
return v___x_1782_;
}
}
else
{
lean_object* v___x_1785_; 
lean_dec(v_k_1770_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1778_);
v___x_1785_ = v___x_1775_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*1, v_hasTrace_1773_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___boxed(lean_object* v_o_1788_, lean_object* v_k_1789_, lean_object* v_v_1790_){
_start:
{
uint8_t v_v_boxed_1791_; lean_object* v_res_1792_; 
v_v_boxed_1791_ = lean_unbox(v_v_1790_);
v_res_1792_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_o_1788_, v_k_1789_, v_v_boxed_1791_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(lean_object* v_opts_1793_, lean_object* v_opt_1794_, uint8_t v_val_1795_){
_start:
{
lean_object* v_name_1796_; lean_object* v___x_1797_; 
v_name_1796_ = lean_ctor_get(v_opt_1794_, 0);
lean_inc(v_name_1796_);
lean_dec_ref(v_opt_1794_);
v___x_1797_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_opts_1793_, v_name_1796_, v_val_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object* v_opts_1798_, lean_object* v_opt_1799_, lean_object* v_val_1800_){
_start:
{
uint8_t v_val_boxed_1801_; lean_object* v_res_1802_; 
v_val_boxed_1801_ = lean_unbox(v_val_1800_);
v_res_1802_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_opts_1798_, v_opt_1799_, v_val_boxed_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(lean_object* v_as_1803_, size_t v_i_1804_, size_t v_stop_1805_, lean_object* v_b_1806_){
_start:
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_usize_dec_eq(v_i_1804_, v_stop_1805_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v_defValue_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; 
v___x_1808_ = lean_array_uget_borrowed(v_as_1803_, v_i_1804_);
v_defValue_1809_ = lean_ctor_get(v___x_1808_, 1);
v___x_1810_ = lean_unbox(v_defValue_1809_);
lean_inc(v___x_1808_);
v___x_1811_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_b_1806_, v___x_1808_, v___x_1810_);
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = lean_usize_add(v_i_1804_, v___x_1812_);
v_i_1804_ = v___x_1813_;
v_b_1806_ = v___x_1811_;
goto _start;
}
else
{
return v_b_1806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3___boxed(lean_object* v_as_1815_, lean_object* v_i_1816_, lean_object* v_stop_1817_, lean_object* v_b_1818_){
_start:
{
size_t v_i_boxed_1819_; size_t v_stop_boxed_1820_; lean_object* v_res_1821_; 
v_i_boxed_1819_ = lean_unbox_usize(v_i_1816_);
lean_dec(v_i_1816_);
v_stop_boxed_1820_ = lean_unbox_usize(v_stop_1817_);
lean_dec(v_stop_1817_);
v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v_as_1815_, v_i_boxed_1819_, v_stop_boxed_1820_, v_b_1818_);
lean_dec_ref(v_as_1815_);
return v_res_1821_;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1823_ = lean_array_get_size(v___x_1822_);
return v___x_1823_;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1825_ = lean_nat_dec_le(v___x_1824_, v___x_1824_);
return v___x_1825_;
}
}
static size_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1826_; size_t v___x_1827_; 
v___x_1826_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1827_ = lean_usize_of_nat(v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object* v_declName_1828_, lean_object* v___x_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
uint8_t v___y_1836_; lean_object* v___y_1837_; lean_object* v_fileName_1838_; lean_object* v_fileMap_1839_; lean_object* v_currRecDepth_1840_; lean_object* v_ref_1841_; lean_object* v_currNamespace_1842_; lean_object* v_openDecls_1843_; lean_object* v_initHeartbeats_1844_; lean_object* v_maxHeartbeats_1845_; lean_object* v_quotContext_1846_; lean_object* v_currMacroScope_1847_; lean_object* v_cancelTk_x3f_1848_; uint8_t v_suppressElabErrors_1849_; lean_object* v_inheritedTraceOptions_1850_; lean_object* v___y_1851_; lean_object* v___x_1856_; lean_object* v_fileName_1857_; lean_object* v_fileMap_1858_; lean_object* v_options_1859_; lean_object* v_currRecDepth_1860_; lean_object* v_ref_1861_; lean_object* v_currNamespace_1862_; lean_object* v_openDecls_1863_; lean_object* v_initHeartbeats_1864_; lean_object* v_maxHeartbeats_1865_; lean_object* v_quotContext_1866_; lean_object* v_currMacroScope_1867_; lean_object* v_cancelTk_x3f_1868_; uint8_t v_suppressElabErrors_1869_; lean_object* v_inheritedTraceOptions_1870_; uint8_t v___y_1872_; lean_object* v___y_1873_; uint8_t v___y_1874_; lean_object* v___y_1896_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1856_ = lean_st_ref_get(v___y_1833_);
v_fileName_1857_ = lean_ctor_get(v___y_1832_, 0);
lean_inc_ref(v_fileName_1857_);
v_fileMap_1858_ = lean_ctor_get(v___y_1832_, 1);
lean_inc_ref(v_fileMap_1858_);
v_options_1859_ = lean_ctor_get(v___y_1832_, 2);
lean_inc_ref(v_options_1859_);
v_currRecDepth_1860_ = lean_ctor_get(v___y_1832_, 3);
lean_inc(v_currRecDepth_1860_);
v_ref_1861_ = lean_ctor_get(v___y_1832_, 5);
lean_inc(v_ref_1861_);
v_currNamespace_1862_ = lean_ctor_get(v___y_1832_, 6);
lean_inc(v_currNamespace_1862_);
v_openDecls_1863_ = lean_ctor_get(v___y_1832_, 7);
lean_inc(v_openDecls_1863_);
v_initHeartbeats_1864_ = lean_ctor_get(v___y_1832_, 8);
lean_inc(v_initHeartbeats_1864_);
v_maxHeartbeats_1865_ = lean_ctor_get(v___y_1832_, 9);
lean_inc(v_maxHeartbeats_1865_);
v_quotContext_1866_ = lean_ctor_get(v___y_1832_, 10);
lean_inc(v_quotContext_1866_);
v_currMacroScope_1867_ = lean_ctor_get(v___y_1832_, 11);
lean_inc(v_currMacroScope_1867_);
v_cancelTk_x3f_1868_ = lean_ctor_get(v___y_1832_, 12);
lean_inc(v_cancelTk_x3f_1868_);
v_suppressElabErrors_1869_ = lean_ctor_get_uint8(v___y_1832_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1870_ = lean_ctor_get(v___y_1832_, 13);
lean_inc_ref(v_inheritedTraceOptions_1870_);
lean_dec_ref(v___y_1832_);
v___x_1901_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1902_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1903_ = lean_nat_dec_lt(v___x_1829_, v___x_1902_);
if (v___x_1903_ == 0)
{
v___y_1896_ = v_options_1859_;
goto v___jp_1895_;
}
else
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_uint8_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1);
if (v___x_1904_ == 0)
{
if (v___x_1903_ == 0)
{
v___y_1896_ = v_options_1859_;
goto v___jp_1895_;
}
else
{
size_t v___x_1905_; size_t v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = ((size_t)0ULL);
v___x_1906_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1901_, v___x_1905_, v___x_1906_, v_options_1859_);
v___y_1896_ = v___x_1907_;
goto v___jp_1895_;
}
}
else
{
size_t v___x_1908_; size_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = ((size_t)0ULL);
v___x_1909_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1901_, v___x_1908_, v___x_1909_, v_options_1859_);
v___y_1896_ = v___x_1910_;
goto v___jp_1895_;
}
}
v___jp_1835_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1852_ = l_Lean_maxRecDepth;
v___x_1853_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v___y_1837_, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1854_, 0, v_fileName_1838_);
lean_ctor_set(v___x_1854_, 1, v_fileMap_1839_);
lean_ctor_set(v___x_1854_, 2, v___y_1837_);
lean_ctor_set(v___x_1854_, 3, v_currRecDepth_1840_);
lean_ctor_set(v___x_1854_, 4, v___x_1853_);
lean_ctor_set(v___x_1854_, 5, v_ref_1841_);
lean_ctor_set(v___x_1854_, 6, v_currNamespace_1842_);
lean_ctor_set(v___x_1854_, 7, v_openDecls_1843_);
lean_ctor_set(v___x_1854_, 8, v_initHeartbeats_1844_);
lean_ctor_set(v___x_1854_, 9, v_maxHeartbeats_1845_);
lean_ctor_set(v___x_1854_, 10, v_quotContext_1846_);
lean_ctor_set(v___x_1854_, 11, v_currMacroScope_1847_);
lean_ctor_set(v___x_1854_, 12, v_cancelTk_x3f_1848_);
lean_ctor_set(v___x_1854_, 13, v_inheritedTraceOptions_1850_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*14, v___y_1836_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*14 + 1, v_suppressElabErrors_1849_);
v___x_1855_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1828_, v___y_1830_, v___y_1831_, v___x_1854_, v___y_1851_);
return v___x_1855_;
}
v___jp_1871_:
{
if (v___y_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v_env_1876_; lean_object* v_nextMacroScope_1877_; lean_object* v_ngen_1878_; lean_object* v_auxDeclNGen_1879_; lean_object* v_traceState_1880_; lean_object* v_messages_1881_; lean_object* v_infoState_1882_; lean_object* v_snapshotTasks_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1893_; 
v___x_1875_ = lean_st_ref_take(v___y_1833_);
v_env_1876_ = lean_ctor_get(v___x_1875_, 0);
v_nextMacroScope_1877_ = lean_ctor_get(v___x_1875_, 1);
v_ngen_1878_ = lean_ctor_get(v___x_1875_, 2);
v_auxDeclNGen_1879_ = lean_ctor_get(v___x_1875_, 3);
v_traceState_1880_ = lean_ctor_get(v___x_1875_, 4);
v_messages_1881_ = lean_ctor_get(v___x_1875_, 6);
v_infoState_1882_ = lean_ctor_get(v___x_1875_, 7);
v_snapshotTasks_1883_ = lean_ctor_get(v___x_1875_, 8);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1875_, 5);
lean_dec(v_unused_1894_);
v___x_1885_ = v___x_1875_;
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snapshotTasks_1883_);
lean_inc(v_infoState_1882_);
lean_inc(v_messages_1881_);
lean_inc(v_traceState_1880_);
lean_inc(v_auxDeclNGen_1879_);
lean_inc(v_ngen_1878_);
lean_inc(v_nextMacroScope_1877_);
lean_inc(v_env_1876_);
lean_dec(v___x_1875_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = l_Lean_Kernel_enableDiag(v_env_1876_, v___y_1872_);
v___x_1888_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 5, v___x_1888_);
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_nextMacroScope_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_ngen_1878_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_auxDeclNGen_1879_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_traceState_1880_);
lean_ctor_set(v_reuseFailAlloc_1892_, 5, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1892_, 6, v_messages_1881_);
lean_ctor_set(v_reuseFailAlloc_1892_, 7, v_infoState_1882_);
lean_ctor_set(v_reuseFailAlloc_1892_, 8, v_snapshotTasks_1883_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_st_ref_set(v___y_1833_, v___x_1890_);
v___y_1836_ = v___y_1872_;
v___y_1837_ = v___y_1873_;
v_fileName_1838_ = v_fileName_1857_;
v_fileMap_1839_ = v_fileMap_1858_;
v_currRecDepth_1840_ = v_currRecDepth_1860_;
v_ref_1841_ = v_ref_1861_;
v_currNamespace_1842_ = v_currNamespace_1862_;
v_openDecls_1843_ = v_openDecls_1863_;
v_initHeartbeats_1844_ = v_initHeartbeats_1864_;
v_maxHeartbeats_1845_ = v_maxHeartbeats_1865_;
v_quotContext_1846_ = v_quotContext_1866_;
v_currMacroScope_1847_ = v_currMacroScope_1867_;
v_cancelTk_x3f_1848_ = v_cancelTk_x3f_1868_;
v_suppressElabErrors_1849_ = v_suppressElabErrors_1869_;
v_inheritedTraceOptions_1850_ = v_inheritedTraceOptions_1870_;
v___y_1851_ = v___y_1833_;
goto v___jp_1835_;
}
}
}
else
{
v___y_1836_ = v___y_1872_;
v___y_1837_ = v___y_1873_;
v_fileName_1838_ = v_fileName_1857_;
v_fileMap_1839_ = v_fileMap_1858_;
v_currRecDepth_1840_ = v_currRecDepth_1860_;
v_ref_1841_ = v_ref_1861_;
v_currNamespace_1842_ = v_currNamespace_1862_;
v_openDecls_1843_ = v_openDecls_1863_;
v_initHeartbeats_1844_ = v_initHeartbeats_1864_;
v_maxHeartbeats_1845_ = v_maxHeartbeats_1865_;
v_quotContext_1846_ = v_quotContext_1866_;
v_currMacroScope_1847_ = v_currMacroScope_1867_;
v_cancelTk_x3f_1848_ = v_cancelTk_x3f_1868_;
v_suppressElabErrors_1849_ = v_suppressElabErrors_1869_;
v_inheritedTraceOptions_1850_ = v_inheritedTraceOptions_1870_;
v___y_1851_ = v___y_1833_;
goto v___jp_1835_;
}
}
v___jp_1895_:
{
lean_object* v_env_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; uint8_t v___x_1900_; 
v_env_1897_ = lean_ctor_get(v___x_1856_, 0);
lean_inc_ref(v_env_1897_);
lean_dec(v___x_1856_);
v___x_1898_ = l_Lean_diagnostics;
v___x_1899_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___y_1896_, v___x_1898_);
v___x_1900_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1897_);
lean_dec_ref(v_env_1897_);
if (v___x_1900_ == 0)
{
if (v___x_1899_ == 0)
{
v___y_1836_ = v___x_1899_;
v___y_1837_ = v___y_1896_;
v_fileName_1838_ = v_fileName_1857_;
v_fileMap_1839_ = v_fileMap_1858_;
v_currRecDepth_1840_ = v_currRecDepth_1860_;
v_ref_1841_ = v_ref_1861_;
v_currNamespace_1842_ = v_currNamespace_1862_;
v_openDecls_1843_ = v_openDecls_1863_;
v_initHeartbeats_1844_ = v_initHeartbeats_1864_;
v_maxHeartbeats_1845_ = v_maxHeartbeats_1865_;
v_quotContext_1846_ = v_quotContext_1866_;
v_currMacroScope_1847_ = v_currMacroScope_1867_;
v_cancelTk_x3f_1848_ = v_cancelTk_x3f_1868_;
v_suppressElabErrors_1849_ = v_suppressElabErrors_1869_;
v_inheritedTraceOptions_1850_ = v_inheritedTraceOptions_1870_;
v___y_1851_ = v___y_1833_;
goto v___jp_1835_;
}
else
{
v___y_1872_ = v___x_1899_;
v___y_1873_ = v___y_1896_;
v___y_1874_ = v___x_1900_;
goto v___jp_1871_;
}
}
else
{
v___y_1872_ = v___x_1899_;
v___y_1873_ = v___y_1896_;
v___y_1874_ = v___x_1899_;
goto v___jp_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object* v_declName_1911_, lean_object* v___x_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Meta_getEqnsFor_x3f___lam__0(v_declName_1911_, v___x_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___x_1912_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1925_ = lean_unsigned_to_nat(32u);
v___x_1926_ = lean_mk_empty_array_with_capacity(v___x_1925_);
lean_dec_ref(v___x_1926_);
v___x_1927_ = lean_unsigned_to_nat(0u);
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1928_, 0, v_declName_1919_);
lean_closure_set(v___f_1928_, 1, v___x_1927_);
v___x_1929_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1931_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1929_, v___x_1930_, v___f_1928_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(lean_object* v_cls_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_options_1942_; uint8_t v_hasTrace_1943_; 
v_options_1942_ = lean_ctor_get(v___y_1940_, 2);
v_hasTrace_1943_ = lean_ctor_get_uint8(v_options_1942_, sizeof(void*)*1);
if (v_hasTrace_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_dec(v_cls_1939_);
v___x_1944_ = lean_box(v_hasTrace_1943_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
else
{
lean_object* v_inheritedTraceOptions_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_inheritedTraceOptions_1946_ = lean_ctor_get(v___y_1940_, 13);
v___x_1947_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1948_ = l_Lean_Name_append(v___x_1947_, v_cls_1939_);
v___x_1949_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1946_, v_options_1942_, v___x_1948_);
lean_dec(v___x_1948_);
v___x_1950_ = lean_box(v___x_1949_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg___boxed(lean_object* v_cls_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v_cls_1952_, v___y_1953_);
lean_dec_ref(v___y_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1(lean_object* v_cls_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v_cls_1956_, v___y_1959_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___boxed(lean_object* v_cls_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1(v_cls_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(lean_object* v_msgData_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; lean_object* v_env_1977_; lean_object* v___x_1978_; lean_object* v_mctx_1979_; lean_object* v_lctx_1980_; lean_object* v_options_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1976_ = lean_st_ref_get(v___y_1974_);
v_env_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc_ref(v_env_1977_);
lean_dec(v___x_1976_);
v___x_1978_ = lean_st_ref_get(v___y_1972_);
v_mctx_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc_ref(v_mctx_1979_);
lean_dec(v___x_1978_);
v_lctx_1980_ = lean_ctor_get(v___y_1971_, 2);
v_options_1981_ = lean_ctor_get(v___y_1973_, 2);
lean_inc_ref(v_options_1981_);
lean_inc_ref(v_lctx_1980_);
v___x_1982_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1982_, 0, v_env_1977_);
lean_ctor_set(v___x_1982_, 1, v_mctx_1979_);
lean_ctor_set(v___x_1982_, 2, v_lctx_1980_);
lean_ctor_set(v___x_1982_, 3, v_options_1981_);
v___x_1983_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v_msgData_1970_);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2___boxed(lean_object* v_msgData_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msgData_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
return v_res_1991_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1992_; double v___x_1993_; 
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = lean_float_of_nat(v___x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(lean_object* v_cls_1997_, lean_object* v_msg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_ref_2004_; lean_object* v___x_2005_; lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2050_; 
v_ref_2004_ = lean_ctor_get(v___y_2001_, 5);
v___x_2005_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2050_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2050_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v_traceState_2011_; lean_object* v_env_2012_; lean_object* v_nextMacroScope_2013_; lean_object* v_ngen_2014_; lean_object* v_auxDeclNGen_2015_; lean_object* v_cache_2016_; lean_object* v_messages_2017_; lean_object* v_infoState_2018_; lean_object* v_snapshotTasks_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2049_; 
v___x_2010_ = lean_st_ref_take(v___y_2002_);
v_traceState_2011_ = lean_ctor_get(v___x_2010_, 4);
v_env_2012_ = lean_ctor_get(v___x_2010_, 0);
v_nextMacroScope_2013_ = lean_ctor_get(v___x_2010_, 1);
v_ngen_2014_ = lean_ctor_get(v___x_2010_, 2);
v_auxDeclNGen_2015_ = lean_ctor_get(v___x_2010_, 3);
v_cache_2016_ = lean_ctor_get(v___x_2010_, 5);
v_messages_2017_ = lean_ctor_get(v___x_2010_, 6);
v_infoState_2018_ = lean_ctor_get(v___x_2010_, 7);
v_snapshotTasks_2019_ = lean_ctor_get(v___x_2010_, 8);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2021_ = v___x_2010_;
v_isShared_2022_ = v_isSharedCheck_2049_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_snapshotTasks_2019_);
lean_inc(v_infoState_2018_);
lean_inc(v_messages_2017_);
lean_inc(v_cache_2016_);
lean_inc(v_traceState_2011_);
lean_inc(v_auxDeclNGen_2015_);
lean_inc(v_ngen_2014_);
lean_inc(v_nextMacroScope_2013_);
lean_inc(v_env_2012_);
lean_dec(v___x_2010_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2049_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
uint64_t v_tid_2023_; lean_object* v_traces_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2048_; 
v_tid_2023_ = lean_ctor_get_uint64(v_traceState_2011_, sizeof(void*)*1);
v_traces_2024_ = lean_ctor_get(v_traceState_2011_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_traceState_2011_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2026_ = v_traceState_2011_;
v_isShared_2027_ = v_isSharedCheck_2048_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_traces_2024_);
lean_dec(v_traceState_2011_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2048_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; double v___x_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0);
v___x_2030_ = 0;
v___x_2031_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1));
v___x_2032_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2032_, 0, v_cls_1997_);
lean_ctor_set(v___x_2032_, 1, v___x_2028_);
lean_ctor_set(v___x_2032_, 2, v___x_2031_);
lean_ctor_set_float(v___x_2032_, sizeof(void*)*3, v___x_2029_);
lean_ctor_set_float(v___x_2032_, sizeof(void*)*3 + 8, v___x_2029_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*3 + 16, v___x_2030_);
v___x_2033_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__2));
v___x_2034_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v_a_2006_);
lean_ctor_set(v___x_2034_, 2, v___x_2033_);
lean_inc(v_ref_2004_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_ref_2004_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_PersistentArray_push___redArg(v_traces_2024_, v___x_2035_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2036_);
v___x_2038_ = v___x_2026_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2036_);
lean_ctor_set_uint64(v_reuseFailAlloc_2047_, sizeof(void*)*1, v_tid_2023_);
v___x_2038_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v___x_2038_);
v___x_2040_ = v___x_2021_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_env_2012_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_nextMacroScope_2013_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_ngen_2014_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_auxDeclNGen_2015_);
lean_ctor_set(v_reuseFailAlloc_2046_, 4, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2046_, 5, v_cache_2016_);
lean_ctor_set(v_reuseFailAlloc_2046_, 6, v_messages_2017_);
lean_ctor_set(v_reuseFailAlloc_2046_, 7, v_infoState_2018_);
lean_ctor_set(v_reuseFailAlloc_2046_, 8, v_snapshotTasks_2019_);
v___x_2040_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2041_ = lean_st_ref_set(v___y_2002_, v___x_2040_);
v___x_2042_ = lean_box(0);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2042_);
v___x_2044_ = v___x_2008_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___boxed(lean_object* v_cls_2051_, lean_object* v_msg_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(v_cls_2051_, v_msg_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(lean_object* v___x_2059_, lean_object* v_as_2060_, size_t v_i_2061_, size_t v_stop_2062_){
_start:
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_usize_dec_eq(v_i_2061_, v_stop_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v_defValue_2065_; uint8_t v___x_2066_; uint8_t v___y_2072_; uint8_t v___x_2073_; 
v___x_2064_ = lean_array_uget_borrowed(v_as_2060_, v_i_2061_);
v_defValue_2065_ = lean_ctor_get(v___x_2064_, 1);
v___x_2066_ = 1;
v___x_2073_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___x_2059_, v___x_2064_);
if (v___x_2073_ == 0)
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_unbox(v_defValue_2065_);
if (v___x_2074_ == 0)
{
goto v___jp_2067_;
}
else
{
v___y_2072_ = v___x_2073_;
goto v___jp_2071_;
}
}
else
{
uint8_t v___x_2075_; 
v___x_2075_ = lean_unbox(v_defValue_2065_);
v___y_2072_ = v___x_2075_;
goto v___jp_2071_;
}
v___jp_2067_:
{
if (v___x_2063_ == 0)
{
size_t v___x_2068_; size_t v___x_2069_; 
v___x_2068_ = ((size_t)1ULL);
v___x_2069_ = lean_usize_add(v_i_2061_, v___x_2068_);
v_i_2061_ = v___x_2069_;
goto _start;
}
else
{
return v___x_2066_;
}
}
v___jp_2071_:
{
if (v___y_2072_ == 0)
{
return v___x_2066_;
}
else
{
goto v___jp_2067_;
}
}
}
else
{
uint8_t v___x_2076_; 
v___x_2076_ = 0;
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object* v___x_2077_, lean_object* v_as_2078_, lean_object* v_i_2079_, lean_object* v_stop_2080_){
_start:
{
size_t v_i_boxed_2081_; size_t v_stop_boxed_2082_; uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_i_boxed_2081_ = lean_unbox_usize(v_i_2079_);
lean_dec(v_i_2079_);
v_stop_boxed_2082_ = lean_unbox_usize(v_stop_2080_);
lean_dec(v_stop_2080_);
v_res_2083_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v___x_2077_, v_as_2078_, v_i_boxed_2081_, v_stop_boxed_2082_);
lean_dec_ref(v_as_2078_);
lean_dec_ref(v___x_2077_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
static uint8_t _init_l_Lean_Meta_generateEagerEqns___closed__0(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2085_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_nat_dec_lt(v___x_2086_, v___x_2085_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__5(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__4));
v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object* v_declName_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = l_Lean_Meta_eqnAffectingOptions;
v___x_2130_ = lean_uint8_once(&l_Lean_Meta_generateEagerEqns___closed__0, &l_Lean_Meta_generateEagerEqns___closed__0_once, _init_l_Lean_Meta_generateEagerEqns___closed__0);
if (v___x_2130_ == 0)
{
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_declName_2097_);
goto v___jp_2103_;
}
else
{
if (v___x_2130_ == 0)
{
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_declName_2097_);
goto v___jp_2103_;
}
else
{
lean_object* v_options_2131_; size_t v___x_2132_; size_t v___x_2133_; uint8_t v___x_2134_; 
v_options_2131_ = lean_ctor_get(v_a_2100_, 2);
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v_options_2131_, v___x_2129_, v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_declName_2097_);
goto v___jp_2103_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_a_2137_; uint8_t v___x_2138_; 
v___x_2135_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_2136_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v___x_2135_, v_a_2100_);
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
v___x_2138_ = lean_unbox(v_a_2137_);
lean_dec(v_a_2137_);
if (v___x_2138_ == 0)
{
v___y_2107_ = v_a_2098_;
v___y_2108_ = v_a_2099_;
v___y_2109_ = v_a_2100_;
v___y_2110_ = v_a_2101_;
goto v___jp_2106_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__5, &l_Lean_Meta_generateEagerEqns___closed__5_once, _init_l_Lean_Meta_generateEagerEqns___closed__5);
lean_inc(v_declName_2097_);
v___x_2140_ = l_Lean_MessageData_ofName(v_declName_2097_);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(v___x_2135_, v___x_2141_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_dec_ref(v___x_2142_);
v___y_2107_ = v_a_2098_;
v___y_2108_ = v_a_2099_;
v___y_2109_ = v_a_2100_;
v___y_2110_ = v_a_2101_;
goto v___jp_2106_;
}
else
{
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_declName_2097_);
return v___x_2142_;
}
}
}
}
}
v___jp_2103_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
v___jp_2106_:
{
lean_object* v___x_2111_; 
v___x_2111_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_2097_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2119_; 
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v___x_2111_, 0);
lean_dec(v_unused_2120_);
v___x_2113_ = v___x_2111_;
v_isShared_2114_ = v_isSharedCheck_2119_;
goto v_resetjp_2112_;
}
else
{
lean_dec(v___x_2111_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2119_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_box(0);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2115_);
v___x_2117_ = v___x_2113_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_a_2121_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2111_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2111_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___boxed(lean_object* v_declName_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_Meta_generateEagerEqns(v_declName_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_st_mk_ref(v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2156_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2175_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2175_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2175_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_unbox(v_a_2159_);
lean_dec(v_a_2159_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_dec_ref(v_f_2156_);
v___x_2164_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2162_ == 0)
{
lean_ctor_set_tag(v___x_2161_, 1);
lean_ctor_set(v___x_2161_, 0, v___x_2164_);
v___x_2166_ = v___x_2161_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2168_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2169_ = lean_st_ref_take(v___x_2168_);
v___x_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_f_2156_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_st_ref_set(v___x_2168_, v___x_2170_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2171_);
v___x_2173_ = v___x_2161_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_f_2156_);
v_a_2176_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2158_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2158_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2190_, lean_object* v_as_x27_2191_, lean_object* v_b_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
if (lean_obj_tag(v_as_x27_2191_) == 0)
{
lean_object* v___x_2198_; 
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v_declName_2190_);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v_b_2192_);
return v___x_2198_;
}
else
{
lean_object* v_head_2199_; lean_object* v_tail_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_b_2192_);
v_head_2199_ = lean_ctor_get(v_as_x27_2191_, 0);
v_tail_2200_ = lean_ctor_get(v_as_x27_2191_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_as_x27_2191_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2202_ = v_as_x27_2191_;
v_isShared_2203_ = v_isSharedCheck_2228_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_tail_2200_);
lean_inc(v_head_2199_);
lean_dec(v_as_x27_2191_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2228_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; 
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v_declName_2190_);
v___x_2204_ = lean_apply_6(v_head_2199_, v_declName_2190_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, lean_box(0));
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2219_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2219_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2219_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_box(0);
if (lean_obj_tag(v_a_2205_) == 1)
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
lean_dec(v_tail_2200_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v_declName_2190_);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v_a_2205_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set_tag(v___x_2202_, 0);
lean_ctor_set(v___x_2202_, 1, v___x_2209_);
lean_ctor_set(v___x_2202_, 0, v___x_2210_);
v___x_2212_ = v___x_2202_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v___x_2209_);
v___x_2212_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2214_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2212_);
v___x_2214_ = v___x_2207_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
lean_object* v___x_2217_; 
lean_del_object(v___x_2207_);
lean_dec(v_a_2205_);
lean_del_object(v___x_2202_);
v___x_2217_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2191_ = v_tail_2200_;
v_b_2192_ = v___x_2217_;
goto _start;
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_del_object(v___x_2202_);
lean_dec(v_tail_2200_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v_declName_2190_);
v_a_2220_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2204_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2204_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2229_, lean_object* v_as_x27_2230_, lean_object* v_b_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2229_, v_as_x27_2230_, v_b_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2238_, lean_object* v_declName_2239_, uint8_t v_nonRec_2240_, lean_object* v___x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2250_; lean_object* v_env_2251_; uint8_t v___x_2252_; uint8_t v___x_2253_; 
v___x_2250_ = lean_st_ref_get(v___y_2245_);
v_env_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref(v_env_2251_);
lean_dec(v___x_2250_);
v___x_2252_ = 1;
lean_inc(v___x_2238_);
v___x_2253_ = l_Lean_Environment_contains(v_env_2251_, v___x_2238_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec(v___x_2238_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
lean_inc(v___y_2243_);
lean_inc_ref(v___y_2242_);
lean_inc(v_declName_2239_);
v___x_2254_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2239_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; uint8_t v___x_2256_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = lean_unbox(v_a_2255_);
lean_dec(v_a_2255_);
if (v___x_2256_ == 0)
{
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___x_2241_);
lean_dec(v_declName_2239_);
goto v___jp_2247_;
}
else
{
lean_object* v___x_2257_; 
lean_inc(v_declName_2239_);
v___x_2257_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2239_, v___y_2245_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; uint8_t v___x_2259_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = lean_unbox(v_a_2258_);
lean_dec(v_a_2258_);
if (v___x_2259_ == 0)
{
if (v_nonRec_2240_ == 0)
{
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___x_2241_);
lean_dec(v_declName_2239_);
goto v___jp_2247_;
}
else
{
lean_object* v___x_2260_; lean_object* v_env_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2260_ = lean_st_ref_get(v___y_2245_);
v_env_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc_ref(v_env_2261_);
lean_dec(v___x_2260_);
lean_inc(v_declName_2239_);
v___x_2262_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2261_, v_declName_2239_, v___x_2241_);
v___x_2263_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2239_, v___x_2262_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2263_;
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref(v___x_2241_);
v___x_2264_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2265_ = lean_st_ref_get(v___x_2264_);
v___x_2266_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2267_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2239_, v___x_2265_, v___x_2266_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2277_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2277_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2277_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v_fst_2272_; 
v_fst_2272_ = lean_ctor_get(v_a_2268_, 0);
lean_inc(v_fst_2272_);
lean_dec(v_a_2268_);
if (lean_obj_tag(v_fst_2272_) == 0)
{
lean_del_object(v___x_2270_);
goto v___jp_2247_;
}
else
{
lean_object* v_val_2273_; lean_object* v___x_2275_; 
v_val_2273_ = lean_ctor_get(v_fst_2272_, 0);
lean_inc(v_val_2273_);
lean_dec_ref(v_fst_2272_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v_val_2273_);
v___x_2275_ = v___x_2270_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_val_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_a_2278_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2267_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2267_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___x_2241_);
lean_dec(v_declName_2239_);
v_a_2286_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2257_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2257_);
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
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___x_2241_);
lean_dec(v_declName_2239_);
v_a_2294_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2254_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2254_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___x_2241_);
lean_dec(v_declName_2239_);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2238_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
v___jp_2247_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2304_, lean_object* v_declName_2305_, lean_object* v_nonRec_2306_, lean_object* v___x_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
uint8_t v_nonRec_boxed_2313_; lean_object* v_res_2314_; 
v_nonRec_boxed_2313_ = lean_unbox(v_nonRec_2306_);
v_res_2314_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2304_, v_declName_2305_, v_nonRec_boxed_2313_, v___x_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_ref_2321_; lean_object* v___x_2322_; lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2331_; 
v_ref_2321_ = lean_ctor_get(v___y_2318_, 5);
v___x_2322_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msg_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2331_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2331_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_inc(v_ref_2321_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_ref_2321_);
lean_ctor_set(v___x_2327_, 1, v_a_2323_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set_tag(v___x_2325_, 1);
lean_ctor_set(v___x_2325_, 0, v___x_2327_);
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2339_, uint8_t v_isExporting_2340_, lean_object* v___x_2341_, lean_object* v___y_2342_, lean_object* v___x_2343_, lean_object* v_a_x3f_2344_){
_start:
{
lean_object* v___x_2346_; lean_object* v_env_2347_; lean_object* v_nextMacroScope_2348_; lean_object* v_ngen_2349_; lean_object* v_auxDeclNGen_2350_; lean_object* v_traceState_2351_; lean_object* v_messages_2352_; lean_object* v_infoState_2353_; lean_object* v_snapshotTasks_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2379_; 
v___x_2346_ = lean_st_ref_take(v___y_2339_);
v_env_2347_ = lean_ctor_get(v___x_2346_, 0);
v_nextMacroScope_2348_ = lean_ctor_get(v___x_2346_, 1);
v_ngen_2349_ = lean_ctor_get(v___x_2346_, 2);
v_auxDeclNGen_2350_ = lean_ctor_get(v___x_2346_, 3);
v_traceState_2351_ = lean_ctor_get(v___x_2346_, 4);
v_messages_2352_ = lean_ctor_get(v___x_2346_, 6);
v_infoState_2353_ = lean_ctor_get(v___x_2346_, 7);
v_snapshotTasks_2354_ = lean_ctor_get(v___x_2346_, 8);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2379_ == 0)
{
lean_object* v_unused_2380_; 
v_unused_2380_ = lean_ctor_get(v___x_2346_, 5);
lean_dec(v_unused_2380_);
v___x_2356_ = v___x_2346_;
v_isShared_2357_ = v_isSharedCheck_2379_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_snapshotTasks_2354_);
lean_inc(v_infoState_2353_);
lean_inc(v_messages_2352_);
lean_inc(v_traceState_2351_);
lean_inc(v_auxDeclNGen_2350_);
lean_inc(v_ngen_2349_);
lean_inc(v_nextMacroScope_2348_);
lean_inc(v_env_2347_);
lean_dec(v___x_2346_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2379_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = l_Lean_Environment_setExporting(v_env_2347_, v_isExporting_2340_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 5, v___x_2341_);
lean_ctor_set(v___x_2356_, 0, v___x_2358_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_nextMacroScope_2348_);
lean_ctor_set(v_reuseFailAlloc_2378_, 2, v_ngen_2349_);
lean_ctor_set(v_reuseFailAlloc_2378_, 3, v_auxDeclNGen_2350_);
lean_ctor_set(v_reuseFailAlloc_2378_, 4, v_traceState_2351_);
lean_ctor_set(v_reuseFailAlloc_2378_, 5, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2378_, 6, v_messages_2352_);
lean_ctor_set(v_reuseFailAlloc_2378_, 7, v_infoState_2353_);
lean_ctor_set(v_reuseFailAlloc_2378_, 8, v_snapshotTasks_2354_);
v___x_2360_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_mctx_2363_; lean_object* v_zetaDeltaFVarIds_2364_; lean_object* v_postponed_2365_; lean_object* v_diag_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2376_; 
v___x_2361_ = lean_st_ref_set(v___y_2339_, v___x_2360_);
v___x_2362_ = lean_st_ref_take(v___y_2342_);
v_mctx_2363_ = lean_ctor_get(v___x_2362_, 0);
v_zetaDeltaFVarIds_2364_ = lean_ctor_get(v___x_2362_, 2);
v_postponed_2365_ = lean_ctor_get(v___x_2362_, 3);
v_diag_2366_ = lean_ctor_get(v___x_2362_, 4);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v___x_2362_, 1);
lean_dec(v_unused_2377_);
v___x_2368_ = v___x_2362_;
v_isShared_2369_ = v_isSharedCheck_2376_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_diag_2366_);
lean_inc(v_postponed_2365_);
lean_inc(v_zetaDeltaFVarIds_2364_);
lean_inc(v_mctx_2363_);
lean_dec(v___x_2362_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2376_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 1, v___x_2343_);
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_mctx_2363_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_zetaDeltaFVarIds_2364_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_postponed_2365_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_diag_2366_);
v___x_2371_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = lean_st_ref_set(v___y_2342_, v___x_2371_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2381_, lean_object* v_isExporting_2382_, lean_object* v___x_2383_, lean_object* v___y_2384_, lean_object* v___x_2385_, lean_object* v_a_x3f_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v_isExporting_boxed_2388_; lean_object* v_res_2389_; 
v_isExporting_boxed_2388_ = lean_unbox(v_isExporting_2382_);
v_res_2389_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2381_, v_isExporting_boxed_2388_, v___x_2383_, v___y_2384_, v___x_2385_, v_a_x3f_2386_);
lean_dec(v_a_x3f_2386_);
lean_dec(v___y_2384_);
lean_dec(v___y_2381_);
return v_res_2389_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_2391_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
lean_ctor_set(v___x_2391_, 2, v___x_2390_);
lean_ctor_set(v___x_2391_, 3, v___x_2390_);
lean_ctor_set(v___x_2391_, 4, v___x_2390_);
lean_ctor_set(v___x_2391_, 5, v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2392_, uint8_t v_isExporting_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___x_2399_; lean_object* v_env_2400_; uint8_t v_isExporting_2401_; lean_object* v___x_2402_; lean_object* v_env_2403_; lean_object* v_nextMacroScope_2404_; lean_object* v_ngen_2405_; lean_object* v_auxDeclNGen_2406_; lean_object* v_traceState_2407_; lean_object* v_messages_2408_; lean_object* v_infoState_2409_; lean_object* v_snapshotTasks_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2464_; 
v___x_2399_ = lean_st_ref_get(v___y_2397_);
v_env_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc_ref(v_env_2400_);
lean_dec(v___x_2399_);
v_isExporting_2401_ = lean_ctor_get_uint8(v_env_2400_, sizeof(void*)*8);
lean_dec_ref(v_env_2400_);
v___x_2402_ = lean_st_ref_take(v___y_2397_);
v_env_2403_ = lean_ctor_get(v___x_2402_, 0);
v_nextMacroScope_2404_ = lean_ctor_get(v___x_2402_, 1);
v_ngen_2405_ = lean_ctor_get(v___x_2402_, 2);
v_auxDeclNGen_2406_ = lean_ctor_get(v___x_2402_, 3);
v_traceState_2407_ = lean_ctor_get(v___x_2402_, 4);
v_messages_2408_ = lean_ctor_get(v___x_2402_, 6);
v_infoState_2409_ = lean_ctor_get(v___x_2402_, 7);
v_snapshotTasks_2410_ = lean_ctor_get(v___x_2402_, 8);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2402_, 5);
lean_dec(v_unused_2465_);
v___x_2412_ = v___x_2402_;
v_isShared_2413_ = v_isSharedCheck_2464_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_snapshotTasks_2410_);
lean_inc(v_infoState_2409_);
lean_inc(v_messages_2408_);
lean_inc(v_traceState_2407_);
lean_inc(v_auxDeclNGen_2406_);
lean_inc(v_ngen_2405_);
lean_inc(v_nextMacroScope_2404_);
lean_inc(v_env_2403_);
lean_dec(v___x_2402_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2464_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2414_ = l_Lean_Environment_setExporting(v_env_2403_, v_isExporting_2393_);
v___x_2415_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 5, v___x_2415_);
lean_ctor_set(v___x_2412_, 0, v___x_2414_);
v___x_2417_ = v___x_2412_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_nextMacroScope_2404_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_ngen_2405_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_auxDeclNGen_2406_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_traceState_2407_);
lean_ctor_set(v_reuseFailAlloc_2463_, 5, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2463_, 6, v_messages_2408_);
lean_ctor_set(v_reuseFailAlloc_2463_, 7, v_infoState_2409_);
lean_ctor_set(v_reuseFailAlloc_2463_, 8, v_snapshotTasks_2410_);
v___x_2417_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_mctx_2420_; lean_object* v_zetaDeltaFVarIds_2421_; lean_object* v_postponed_2422_; lean_object* v_diag_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2461_; 
v___x_2418_ = lean_st_ref_set(v___y_2397_, v___x_2417_);
v___x_2419_ = lean_st_ref_take(v___y_2395_);
v_mctx_2420_ = lean_ctor_get(v___x_2419_, 0);
v_zetaDeltaFVarIds_2421_ = lean_ctor_get(v___x_2419_, 2);
v_postponed_2422_ = lean_ctor_get(v___x_2419_, 3);
v_diag_2423_ = lean_ctor_get(v___x_2419_, 4);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v___x_2419_, 1);
lean_dec(v_unused_2462_);
v___x_2425_ = v___x_2419_;
v_isShared_2426_ = v_isSharedCheck_2461_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_diag_2423_);
lean_inc(v_postponed_2422_);
lean_inc(v_zetaDeltaFVarIds_2421_);
lean_inc(v_mctx_2420_);
lean_dec(v___x_2419_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2461_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 1, v___x_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_mctx_2420_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_zetaDeltaFVarIds_2421_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_postponed_2422_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_diag_2423_);
v___x_2429_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v_r_2431_; 
v___x_2430_ = lean_st_ref_set(v___y_2395_, v___x_2429_);
lean_inc(v___y_2397_);
lean_inc(v___y_2395_);
v_r_2431_ = lean_apply_5(v_x_2392_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, lean_box(0));
if (lean_obj_tag(v_r_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2448_; 
v_a_2432_ = lean_ctor_get(v_r_2431_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_r_2431_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2434_ = v_r_2431_;
v_isShared_2435_ = v_isSharedCheck_2448_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v_r_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2448_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
lean_inc(v_a_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 1);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
v___x_2438_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2397_, v_isExporting_2401_, v___x_2415_, v___y_2395_, v___x_2427_, v___x_2437_);
lean_dec_ref(v___x_2437_);
lean_dec(v___y_2395_);
lean_dec(v___y_2397_);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; 
v_unused_2446_ = lean_ctor_get(v___x_2438_, 0);
lean_dec(v_unused_2446_);
v___x_2440_ = v___x_2438_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_dec(v___x_2438_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_a_2432_);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2432_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2449_ = lean_ctor_get(v_r_2431_, 0);
lean_inc(v_a_2449_);
lean_dec_ref(v_r_2431_);
v___x_2450_ = lean_box(0);
v___x_2451_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2397_, v_isExporting_2401_, v___x_2415_, v___y_2395_, v___x_2427_, v___x_2450_);
lean_dec(v___y_2395_);
lean_dec(v___y_2397_);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v___x_2451_, 0);
lean_dec(v_unused_2459_);
v___x_2453_ = v___x_2451_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_dec(v___x_2451_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set_tag(v___x_2453_, 1);
lean_ctor_set(v___x_2453_, 0, v_a_2449_);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2449_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2466_, lean_object* v_isExporting_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
uint8_t v_isExporting_boxed_2473_; lean_object* v_res_2474_; 
v_isExporting_boxed_2473_ = lean_unbox(v_isExporting_2467_);
v_res_2474_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2466_, v_isExporting_boxed_2473_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2475_, uint8_t v_when_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
if (v_when_2476_ == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_apply_5(v_x_2475_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, lean_box(0));
return v___x_2482_;
}
else
{
uint8_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = 0;
v___x_2484_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2475_, v___x_2483_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2485_, lean_object* v_when_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
uint8_t v_when_boxed_2492_; lean_object* v_res_2493_; 
v_when_boxed_2492_ = lean_unbox(v_when_2486_);
v_res_2493_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2485_, v_when_boxed_2492_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
return v_res_2493_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2496_ = l_Lean_stringToMessageData(v___x_2495_);
return v___x_2496_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2499_ = l_Lean_stringToMessageData(v___x_2498_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2502_ = l_Lean_stringToMessageData(v___x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2503_, uint8_t v_nonRec_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v_env_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___f_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2510_ = lean_st_ref_get(v___y_2508_);
v_env_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc_ref(v_env_2511_);
lean_dec(v___x_2510_);
v___x_2512_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2503_);
v___x_2513_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2511_, v_declName_2503_, v___x_2512_);
v___x_2514_ = lean_box(v_nonRec_2504_);
lean_inc(v___x_2513_);
v___f_2515_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2515_, 0, v___x_2513_);
lean_closure_set(v___f_2515_, 1, v_declName_2503_);
lean_closure_set(v___f_2515_, 2, v___x_2514_);
lean_closure_set(v___f_2515_, 3, v___x_2512_);
v___x_2516_ = 1;
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
v___x_2517_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2515_, v___x_2516_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
if (lean_obj_tag(v_a_2518_) == 1)
{
lean_object* v_val_2519_; uint8_t v___x_2520_; 
v_val_2519_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_val_2519_);
lean_dec_ref(v_a_2518_);
v___x_2520_ = lean_name_eq(v_val_2519_, v___x_2513_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v___x_2517_);
v___x_2521_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2522_ = l_Lean_MessageData_ofName(v_val_2519_);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = l_Lean_MessageData_ofName(v___x_2513_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2529_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
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
else
{
lean_dec(v_val_2519_);
lean_dec(v___x_2513_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v___x_2517_;
}
}
else
{
lean_dec(v_a_2518_);
lean_dec(v___x_2513_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v___x_2517_;
}
}
else
{
lean_dec(v___x_2513_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2539_, lean_object* v_nonRec_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
uint8_t v_nonRec_boxed_2546_; lean_object* v_res_2547_; 
v_nonRec_boxed_2546_ = lean_unbox(v_nonRec_2540_);
v_res_2547_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2539_, v_nonRec_boxed_2546_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2548_, uint8_t v_nonRec_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2555_; lean_object* v___f_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2555_ = lean_box(v_nonRec_2549_);
v___f_2556_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2556_, 0, v_declName_2548_);
lean_closure_set(v___f_2556_, 1, v___x_2555_);
v___x_2557_ = lean_unsigned_to_nat(32u);
v___x_2558_ = lean_mk_empty_array_with_capacity(v___x_2557_);
lean_dec_ref(v___x_2558_);
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2560_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2561_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2559_, v___x_2560_, v___f_2556_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2562_, lean_object* v_nonRec_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
uint8_t v_nonRec_boxed_2569_; lean_object* v_res_2570_; 
v_nonRec_boxed_2569_ = lean_unbox(v_nonRec_2563_);
v_res_2570_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2562_, v_nonRec_boxed_2569_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2571_, lean_object* v_as_2572_, lean_object* v_as_x27_2573_, lean_object* v_b_2574_, lean_object* v_a_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2571_, v_as_x27_2573_, v_b_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2582_, lean_object* v_as_2583_, lean_object* v_as_x27_2584_, lean_object* v_b_2585_, lean_object* v_a_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2582_, v_as_2583_, v_as_x27_2584_, v_b_2585_, v_a_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v_as_2583_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2593_, lean_object* v_x_2594_, uint8_t v_isExporting_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2594_, v_isExporting_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2602_, lean_object* v_x_2603_, lean_object* v_isExporting_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
uint8_t v_isExporting_boxed_2610_; lean_object* v_res_2611_; 
v_isExporting_boxed_2610_ = lean_unbox(v_isExporting_2604_);
v_res_2611_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2602_, v_x_2603_, v_isExporting_boxed_2610_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2612_, lean_object* v_x_2613_, uint8_t v_when_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2613_, v_when_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2621_, lean_object* v_x_2622_, lean_object* v_when_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
uint8_t v_when_boxed_2629_; lean_object* v_res_2630_; 
v_when_boxed_2629_ = lean_unbox(v_when_2623_);
v_res_2630_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2621_, v_x_2622_, v_when_boxed_2629_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2631_, lean_object* v_msg_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2639_, lean_object* v_msg_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2639_, v_msg_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v_cls_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_options_2650_; uint8_t v_hasTrace_2651_; 
v_options_2650_ = lean_ctor_get(v___y_2648_, 2);
v_hasTrace_2651_ = lean_ctor_get_uint8(v_options_2650_, sizeof(void*)*1);
if (v_hasTrace_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec(v_cls_2647_);
v___x_2652_ = lean_box(v_hasTrace_2651_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
else
{
lean_object* v_inheritedTraceOptions_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_inheritedTraceOptions_2654_ = lean_ctor_get(v___y_2648_, 13);
v___x_2655_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_2656_ = l_Lean_Name_append(v___x_2655_, v_cls_2647_);
v___x_2657_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2654_, v_options_2650_, v___x_2656_);
lean_dec(v___x_2656_);
v___x_2658_ = lean_box(v___x_2657_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_cls_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v_cls_2660_, v___y_2661_);
lean_dec_ref(v___y_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v_cls_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v_cls_2664_, v___y_2665_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v_cls_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v_cls_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
return v_res_2673_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = lean_unsigned_to_nat(32u);
v___x_2675_ = lean_mk_empty_array_with_capacity(v___x_2674_);
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2677_ = ((size_t)5ULL);
v___x_2678_ = lean_unsigned_to_nat(0u);
v___x_2679_ = lean_unsigned_to_nat(32u);
v___x_2680_ = lean_mk_empty_array_with_capacity(v___x_2679_);
v___x_2681_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_2682_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
lean_ctor_set(v___x_2682_, 1, v___x_2680_);
lean_ctor_set(v___x_2682_, 2, v___x_2678_);
lean_ctor_set(v___x_2682_, 3, v___x_2678_);
lean_ctor_set_usize(v___x_2682_, 4, v___x_2677_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; lean_object* v_traceState_2686_; lean_object* v_traces_2687_; lean_object* v___x_2688_; lean_object* v_traceState_2689_; lean_object* v_env_2690_; lean_object* v_nextMacroScope_2691_; lean_object* v_ngen_2692_; lean_object* v_auxDeclNGen_2693_; lean_object* v_cache_2694_; lean_object* v_messages_2695_; lean_object* v_infoState_2696_; lean_object* v_snapshotTasks_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2716_; 
v___x_2685_ = lean_st_ref_get(v___y_2683_);
v_traceState_2686_ = lean_ctor_get(v___x_2685_, 4);
lean_inc_ref(v_traceState_2686_);
lean_dec(v___x_2685_);
v_traces_2687_ = lean_ctor_get(v_traceState_2686_, 0);
lean_inc_ref(v_traces_2687_);
lean_dec_ref(v_traceState_2686_);
v___x_2688_ = lean_st_ref_take(v___y_2683_);
v_traceState_2689_ = lean_ctor_get(v___x_2688_, 4);
v_env_2690_ = lean_ctor_get(v___x_2688_, 0);
v_nextMacroScope_2691_ = lean_ctor_get(v___x_2688_, 1);
v_ngen_2692_ = lean_ctor_get(v___x_2688_, 2);
v_auxDeclNGen_2693_ = lean_ctor_get(v___x_2688_, 3);
v_cache_2694_ = lean_ctor_get(v___x_2688_, 5);
v_messages_2695_ = lean_ctor_get(v___x_2688_, 6);
v_infoState_2696_ = lean_ctor_get(v___x_2688_, 7);
v_snapshotTasks_2697_ = lean_ctor_get(v___x_2688_, 8);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2699_ = v___x_2688_;
v_isShared_2700_ = v_isSharedCheck_2716_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_snapshotTasks_2697_);
lean_inc(v_infoState_2696_);
lean_inc(v_messages_2695_);
lean_inc(v_cache_2694_);
lean_inc(v_traceState_2689_);
lean_inc(v_auxDeclNGen_2693_);
lean_inc(v_ngen_2692_);
lean_inc(v_nextMacroScope_2691_);
lean_inc(v_env_2690_);
lean_dec(v___x_2688_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2716_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
uint64_t v_tid_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2714_; 
v_tid_2701_ = lean_ctor_get_uint64(v_traceState_2689_, sizeof(void*)*1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_traceState_2689_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; 
v_unused_2715_ = lean_ctor_get(v_traceState_2689_, 0);
lean_dec(v_unused_2715_);
v___x_2703_ = v_traceState_2689_;
v_isShared_2704_ = v_isSharedCheck_2714_;
goto v_resetjp_2702_;
}
else
{
lean_dec(v_traceState_2689_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2714_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2705_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2705_);
v___x_2707_ = v___x_2703_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2705_);
lean_ctor_set_uint64(v_reuseFailAlloc_2713_, sizeof(void*)*1, v_tid_2701_);
v___x_2707_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2709_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 4, v___x_2707_);
v___x_2709_ = v___x_2699_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_env_2690_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_nextMacroScope_2691_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_ngen_2692_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_auxDeclNGen_2693_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2712_, 5, v_cache_2694_);
lean_ctor_set(v_reuseFailAlloc_2712_, 6, v_messages_2695_);
lean_ctor_set(v_reuseFailAlloc_2712_, 7, v_infoState_2696_);
lean_ctor_set(v_reuseFailAlloc_2712_, 8, v_snapshotTasks_2697_);
v___x_2709_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_st_ref_set(v___y_2683_, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_traces_2687_);
return v___x_2711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_2717_);
lean_dec(v___y_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2732_ = 0;
v___x_2733_ = lean_box(v___x_2732_);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2739_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2742_ = l_Lean_stringToMessageData(v___x_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2748_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2749_ = l_Lean_MessageData_ofName(v_name_2743_);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2752_, lean_object* v_x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2752_, v_x_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v_x_2753_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_a_2760_ = lean_ctor_get(v_x_2758_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v_x_2758_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v_x_2758_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 1);
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_a_2768_ = lean_ctor_get(v_x_2758_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v_x_2758_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v_x_2758_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_x_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_x_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(size_t v_sz_2779_, size_t v_i_2780_, lean_object* v_bs_2781_){
_start:
{
uint8_t v___x_2782_; 
v___x_2782_ = lean_usize_dec_lt(v_i_2780_, v_sz_2779_);
if (v___x_2782_ == 0)
{
return v_bs_2781_;
}
else
{
lean_object* v_v_2783_; lean_object* v_msg_2784_; lean_object* v___x_2785_; lean_object* v_bs_x27_2786_; size_t v___x_2787_; size_t v___x_2788_; lean_object* v___x_2789_; 
v_v_2783_ = lean_array_uget_borrowed(v_bs_2781_, v_i_2780_);
v_msg_2784_ = lean_ctor_get(v_v_2783_, 1);
lean_inc_ref(v_msg_2784_);
v___x_2785_ = lean_unsigned_to_nat(0u);
v_bs_x27_2786_ = lean_array_uset(v_bs_2781_, v_i_2780_, v___x_2785_);
v___x_2787_ = ((size_t)1ULL);
v___x_2788_ = lean_usize_add(v_i_2780_, v___x_2787_);
v___x_2789_ = lean_array_uset(v_bs_x27_2786_, v_i_2780_, v_msg_2784_);
v_i_2780_ = v___x_2788_;
v_bs_2781_ = v___x_2789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_sz_2791_, lean_object* v_i_2792_, lean_object* v_bs_2793_){
_start:
{
size_t v_sz_boxed_2794_; size_t v_i_boxed_2795_; lean_object* v_res_2796_; 
v_sz_boxed_2794_ = lean_unbox_usize(v_sz_2791_);
lean_dec(v_sz_2791_);
v_i_boxed_2795_ = lean_unbox_usize(v_i_2792_);
lean_dec(v_i_2792_);
v_res_2796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_sz_boxed_2794_, v_i_boxed_2795_, v_bs_2793_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_oldTraces_2797_, lean_object* v_data_2798_, lean_object* v_ref_2799_, lean_object* v_msg_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_fileName_2804_; lean_object* v_fileMap_2805_; lean_object* v_options_2806_; lean_object* v_currRecDepth_2807_; lean_object* v_maxRecDepth_2808_; lean_object* v_ref_2809_; lean_object* v_currNamespace_2810_; lean_object* v_openDecls_2811_; lean_object* v_initHeartbeats_2812_; lean_object* v_maxHeartbeats_2813_; lean_object* v_quotContext_2814_; lean_object* v_currMacroScope_2815_; uint8_t v_diag_2816_; lean_object* v_cancelTk_x3f_2817_; uint8_t v_suppressElabErrors_2818_; lean_object* v_inheritedTraceOptions_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2874_; 
v_fileName_2804_ = lean_ctor_get(v___y_2801_, 0);
v_fileMap_2805_ = lean_ctor_get(v___y_2801_, 1);
v_options_2806_ = lean_ctor_get(v___y_2801_, 2);
v_currRecDepth_2807_ = lean_ctor_get(v___y_2801_, 3);
v_maxRecDepth_2808_ = lean_ctor_get(v___y_2801_, 4);
v_ref_2809_ = lean_ctor_get(v___y_2801_, 5);
v_currNamespace_2810_ = lean_ctor_get(v___y_2801_, 6);
v_openDecls_2811_ = lean_ctor_get(v___y_2801_, 7);
v_initHeartbeats_2812_ = lean_ctor_get(v___y_2801_, 8);
v_maxHeartbeats_2813_ = lean_ctor_get(v___y_2801_, 9);
v_quotContext_2814_ = lean_ctor_get(v___y_2801_, 10);
v_currMacroScope_2815_ = lean_ctor_get(v___y_2801_, 11);
v_diag_2816_ = lean_ctor_get_uint8(v___y_2801_, sizeof(void*)*14);
v_cancelTk_x3f_2817_ = lean_ctor_get(v___y_2801_, 12);
v_suppressElabErrors_2818_ = lean_ctor_get_uint8(v___y_2801_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2819_ = lean_ctor_get(v___y_2801_, 13);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___y_2801_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2821_ = v___y_2801_;
v_isShared_2822_ = v_isSharedCheck_2874_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_inheritedTraceOptions_2819_);
lean_inc(v_cancelTk_x3f_2817_);
lean_inc(v_currMacroScope_2815_);
lean_inc(v_quotContext_2814_);
lean_inc(v_maxHeartbeats_2813_);
lean_inc(v_initHeartbeats_2812_);
lean_inc(v_openDecls_2811_);
lean_inc(v_currNamespace_2810_);
lean_inc(v_ref_2809_);
lean_inc(v_maxRecDepth_2808_);
lean_inc(v_currRecDepth_2807_);
lean_inc(v_options_2806_);
lean_inc(v_fileMap_2805_);
lean_inc(v_fileName_2804_);
lean_dec(v___y_2801_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2874_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v_traceState_2824_; lean_object* v_traces_2825_; lean_object* v_ref_2826_; lean_object* v___x_2828_; 
v___x_2823_ = lean_st_ref_get(v___y_2802_);
v_traceState_2824_ = lean_ctor_get(v___x_2823_, 4);
lean_inc_ref(v_traceState_2824_);
lean_dec(v___x_2823_);
v_traces_2825_ = lean_ctor_get(v_traceState_2824_, 0);
lean_inc_ref(v_traces_2825_);
lean_dec_ref(v_traceState_2824_);
v_ref_2826_ = l_Lean_replaceRef(v_ref_2799_, v_ref_2809_);
lean_dec(v_ref_2809_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 5, v_ref_2826_);
v___x_2828_ = v___x_2821_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_fileName_2804_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_fileMap_2805_);
lean_ctor_set(v_reuseFailAlloc_2873_, 2, v_options_2806_);
lean_ctor_set(v_reuseFailAlloc_2873_, 3, v_currRecDepth_2807_);
lean_ctor_set(v_reuseFailAlloc_2873_, 4, v_maxRecDepth_2808_);
lean_ctor_set(v_reuseFailAlloc_2873_, 5, v_ref_2826_);
lean_ctor_set(v_reuseFailAlloc_2873_, 6, v_currNamespace_2810_);
lean_ctor_set(v_reuseFailAlloc_2873_, 7, v_openDecls_2811_);
lean_ctor_set(v_reuseFailAlloc_2873_, 8, v_initHeartbeats_2812_);
lean_ctor_set(v_reuseFailAlloc_2873_, 9, v_maxHeartbeats_2813_);
lean_ctor_set(v_reuseFailAlloc_2873_, 10, v_quotContext_2814_);
lean_ctor_set(v_reuseFailAlloc_2873_, 11, v_currMacroScope_2815_);
lean_ctor_set(v_reuseFailAlloc_2873_, 12, v_cancelTk_x3f_2817_);
lean_ctor_set(v_reuseFailAlloc_2873_, 13, v_inheritedTraceOptions_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2873_, sizeof(void*)*14, v_diag_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2873_, sizeof(void*)*14 + 1, v_suppressElabErrors_2818_);
v___x_2828_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; size_t v_sz_2830_; size_t v___x_2831_; lean_object* v___x_2832_; lean_object* v_msg_2833_; lean_object* v___x_2834_; lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2872_; 
v___x_2829_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2825_);
lean_dec_ref(v_traces_2825_);
v_sz_2830_ = lean_array_size(v___x_2829_);
v___x_2831_ = ((size_t)0ULL);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_sz_2830_, v___x_2831_, v___x_2829_);
v_msg_2833_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2833_, 0, v_data_2798_);
lean_ctor_set(v_msg_2833_, 1, v_msg_2800_);
lean_ctor_set(v_msg_2833_, 2, v___x_2832_);
v___x_2834_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2833_, v___x_2828_, v___y_2802_);
lean_dec_ref(v___x_2828_);
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2872_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2872_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v_traceState_2840_; lean_object* v_env_2841_; lean_object* v_nextMacroScope_2842_; lean_object* v_ngen_2843_; lean_object* v_auxDeclNGen_2844_; lean_object* v_cache_2845_; lean_object* v_messages_2846_; lean_object* v_infoState_2847_; lean_object* v_snapshotTasks_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2871_; 
v___x_2839_ = lean_st_ref_take(v___y_2802_);
v_traceState_2840_ = lean_ctor_get(v___x_2839_, 4);
v_env_2841_ = lean_ctor_get(v___x_2839_, 0);
v_nextMacroScope_2842_ = lean_ctor_get(v___x_2839_, 1);
v_ngen_2843_ = lean_ctor_get(v___x_2839_, 2);
v_auxDeclNGen_2844_ = lean_ctor_get(v___x_2839_, 3);
v_cache_2845_ = lean_ctor_get(v___x_2839_, 5);
v_messages_2846_ = lean_ctor_get(v___x_2839_, 6);
v_infoState_2847_ = lean_ctor_get(v___x_2839_, 7);
v_snapshotTasks_2848_ = lean_ctor_get(v___x_2839_, 8);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2850_ = v___x_2839_;
v_isShared_2851_ = v_isSharedCheck_2871_;
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
v_isShared_2851_ = v_isSharedCheck_2871_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
uint64_t v_tid_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2869_; 
v_tid_2852_ = lean_ctor_get_uint64(v_traceState_2840_, sizeof(void*)*1);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_traceState_2840_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v_traceState_2840_, 0);
lean_dec(v_unused_2870_);
v___x_2854_ = v_traceState_2840_;
v_isShared_2855_ = v_isSharedCheck_2869_;
goto v_resetjp_2853_;
}
else
{
lean_dec(v_traceState_2840_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2869_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_ref_2799_);
lean_ctor_set(v___x_2856_, 1, v_a_2835_);
v___x_2857_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2797_, v___x_2856_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2857_);
v___x_2859_ = v___x_2854_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2857_);
lean_ctor_set_uint64(v_reuseFailAlloc_2868_, sizeof(void*)*1, v_tid_2852_);
v___x_2859_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 4, v___x_2859_);
v___x_2861_ = v___x_2850_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_env_2841_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_nextMacroScope_2842_);
lean_ctor_set(v_reuseFailAlloc_2867_, 2, v_ngen_2843_);
lean_ctor_set(v_reuseFailAlloc_2867_, 3, v_auxDeclNGen_2844_);
lean_ctor_set(v_reuseFailAlloc_2867_, 4, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2867_, 5, v_cache_2845_);
lean_ctor_set(v_reuseFailAlloc_2867_, 6, v_messages_2846_);
lean_ctor_set(v_reuseFailAlloc_2867_, 7, v_infoState_2847_);
lean_ctor_set(v_reuseFailAlloc_2867_, 8, v_snapshotTasks_2848_);
v___x_2861_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2862_ = lean_st_ref_set(v___y_2802_, v___x_2861_);
v___x_2863_ = lean_box(0);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2863_);
v___x_2865_ = v___x_2837_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_oldTraces_2875_, lean_object* v_data_2876_, lean_object* v_ref_2877_, lean_object* v_msg_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(v_oldTraces_2875_, v_data_2876_, v_ref_2877_, v_msg_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
return v_res_2882_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(lean_object* v_e_2883_){
_start:
{
if (lean_obj_tag(v_e_2883_) == 0)
{
uint8_t v___x_2884_; 
v___x_2884_ = 2;
return v___x_2884_;
}
else
{
lean_object* v_a_2885_; uint8_t v___x_2886_; 
v_a_2885_ = lean_ctor_get(v_e_2883_, 0);
v___x_2886_ = lean_unbox(v_a_2885_);
if (v___x_2886_ == 0)
{
uint8_t v___x_2887_; 
v___x_2887_ = 1;
return v___x_2887_;
}
else
{
uint8_t v___x_2888_; 
v___x_2888_ = 0;
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2___boxed(lean_object* v_e_2889_){
_start:
{
uint8_t v_res_2890_; lean_object* v_r_2891_; 
v_res_2890_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(v_e_2889_);
lean_dec_ref(v_e_2889_);
v_r_2891_ = lean_box(v_res_2890_);
return v_r_2891_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__0));
v___x_2894_ = l_Lean_stringToMessageData(v___x_2893_);
return v___x_2894_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__2));
v___x_2897_ = l_Lean_stringToMessageData(v___x_2896_);
return v___x_2897_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4(void){
_start:
{
lean_object* v___x_2898_; double v___x_2899_; 
v___x_2898_ = lean_unsigned_to_nat(1000u);
v___x_2899_ = lean_float_of_nat(v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(lean_object* v_cls_2900_, uint8_t v_collapsed_2901_, lean_object* v_tag_2902_, lean_object* v_opts_2903_, uint8_t v_clsEnabled_2904_, lean_object* v_oldTraces_2905_, lean_object* v_msg_2906_, lean_object* v_resStartStop_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_fst_2911_; lean_object* v_snd_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_3010_; 
v_fst_2911_ = lean_ctor_get(v_resStartStop_2907_, 0);
v_snd_2912_ = lean_ctor_get(v_resStartStop_2907_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_resStartStop_2907_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2914_ = v_resStartStop_2907_;
v_isShared_2915_ = v_isSharedCheck_3010_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_snd_2912_);
lean_inc(v_fst_2911_);
lean_dec(v_resStartStop_2907_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_3010_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v_data_2919_; lean_object* v_fst_2930_; lean_object* v_snd_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_3009_; 
v_fst_2930_ = lean_ctor_get(v_snd_2912_, 0);
v_snd_2931_ = lean_ctor_get(v_snd_2912_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_snd_2912_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2933_ = v_snd_2912_;
v_isShared_2934_ = v_isSharedCheck_3009_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_snd_2931_);
lean_inc(v_fst_2930_);
lean_dec(v_snd_2912_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_3009_;
goto v_resetjp_2932_;
}
v___jp_2916_:
{
lean_object* v___x_2920_; 
v___x_2920_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(v_oldTraces_2905_, v_data_2919_, v___y_2917_, v___y_2918_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v___x_2921_; 
lean_dec_ref(v___x_2920_);
v___x_2921_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_fst_2911_);
return v___x_2921_;
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_fst_2911_);
v_a_2922_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2920_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2920_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; uint8_t v___x_2936_; lean_object* v___y_2938_; lean_object* v_a_2939_; uint8_t v___y_2963_; double v___y_2994_; 
v___x_2935_ = l_Lean_trace_profiler;
v___x_2936_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2903_, v___x_2935_);
if (v___x_2936_ == 0)
{
v___y_2963_ = v___x_2936_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3000_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2903_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; double v___x_3003_; double v___x_3004_; double v___x_3005_; 
v___x_3001_ = l_Lean_trace_profiler_threshold;
v___x_3002_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2903_, v___x_3001_);
v___x_3003_ = lean_float_of_nat(v___x_3002_);
v___x_3004_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4);
v___x_3005_ = lean_float_div(v___x_3003_, v___x_3004_);
v___y_2994_ = v___x_3005_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; double v___x_3008_; 
v___x_3006_ = l_Lean_trace_profiler_threshold;
v___x_3007_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2903_, v___x_3006_);
v___x_3008_ = lean_float_of_nat(v___x_3007_);
v___y_2994_ = v___x_3008_;
goto v___jp_2993_;
}
}
v___jp_2937_:
{
uint8_t v_result_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2945_; 
v_result_2940_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(v_fst_2911_);
v___x_2941_ = l_Lean_TraceResult_toEmoji(v_result_2940_);
v___x_2942_ = l_Lean_stringToMessageData(v___x_2941_);
v___x_2943_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1);
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 7);
lean_ctor_set(v___x_2933_, 1, v___x_2943_);
lean_ctor_set(v___x_2933_, 0, v___x_2942_);
v___x_2945_ = v___x_2933_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v_m_2947_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set_tag(v___x_2914_, 7);
lean_ctor_set(v___x_2914_, 1, v_a_2939_);
lean_ctor_set(v___x_2914_, 0, v___x_2945_);
v_m_2947_ = v___x_2914_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_a_2939_);
v_m_2947_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; double v___x_2950_; lean_object* v_data_2951_; 
v___x_2948_ = lean_box(v_result_2940_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
v___x_2950_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0);
lean_inc_ref(v_tag_2902_);
lean_inc_ref(v___x_2949_);
lean_inc(v_cls_2900_);
v_data_2951_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2951_, 0, v_cls_2900_);
lean_ctor_set(v_data_2951_, 1, v___x_2949_);
lean_ctor_set(v_data_2951_, 2, v_tag_2902_);
lean_ctor_set_float(v_data_2951_, sizeof(void*)*3, v___x_2950_);
lean_ctor_set_float(v_data_2951_, sizeof(void*)*3 + 8, v___x_2950_);
lean_ctor_set_uint8(v_data_2951_, sizeof(void*)*3 + 16, v_collapsed_2901_);
if (v___x_2936_ == 0)
{
lean_dec_ref(v___x_2949_);
lean_dec(v_snd_2931_);
lean_dec(v_fst_2930_);
lean_dec_ref(v_tag_2902_);
lean_dec(v_cls_2900_);
v___y_2917_ = v___y_2938_;
v___y_2918_ = v_m_2947_;
v_data_2919_ = v_data_2951_;
goto v___jp_2916_;
}
else
{
lean_object* v_data_2952_; double v___x_2953_; double v___x_2954_; 
lean_dec_ref(v_data_2951_);
v_data_2952_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2952_, 0, v_cls_2900_);
lean_ctor_set(v_data_2952_, 1, v___x_2949_);
lean_ctor_set(v_data_2952_, 2, v_tag_2902_);
v___x_2953_ = lean_unbox_float(v_fst_2930_);
lean_dec(v_fst_2930_);
lean_ctor_set_float(v_data_2952_, sizeof(void*)*3, v___x_2953_);
v___x_2954_ = lean_unbox_float(v_snd_2931_);
lean_dec(v_snd_2931_);
lean_ctor_set_float(v_data_2952_, sizeof(void*)*3 + 8, v___x_2954_);
lean_ctor_set_uint8(v_data_2952_, sizeof(void*)*3 + 16, v_collapsed_2901_);
v___y_2917_ = v___y_2938_;
v___y_2918_ = v_m_2947_;
v_data_2919_ = v_data_2952_;
goto v___jp_2916_;
}
}
}
}
v___jp_2957_:
{
lean_object* v_ref_2958_; lean_object* v___x_2959_; 
v_ref_2958_ = lean_ctor_get(v___y_2908_, 5);
lean_inc(v___y_2909_);
lean_inc_ref(v___y_2908_);
lean_inc(v_fst_2911_);
v___x_2959_ = lean_apply_4(v_msg_2906_, v_fst_2911_, v___y_2908_, v___y_2909_, lean_box(0));
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref(v___x_2959_);
lean_inc(v_ref_2958_);
v___y_2938_ = v_ref_2958_;
v_a_2939_ = v_a_2960_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2961_; 
lean_dec_ref(v___x_2959_);
v___x_2961_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3);
lean_inc(v_ref_2958_);
v___y_2938_ = v_ref_2958_;
v_a_2939_ = v___x_2961_;
goto v___jp_2937_;
}
}
v___jp_2962_:
{
if (v_clsEnabled_2904_ == 0)
{
if (v___y_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v_traceState_2965_; lean_object* v_env_2966_; lean_object* v_nextMacroScope_2967_; lean_object* v_ngen_2968_; lean_object* v_auxDeclNGen_2969_; lean_object* v_cache_2970_; lean_object* v_messages_2971_; lean_object* v_infoState_2972_; lean_object* v_snapshotTasks_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2992_; 
lean_del_object(v___x_2933_);
lean_dec(v_snd_2931_);
lean_dec(v_fst_2930_);
lean_del_object(v___x_2914_);
lean_dec_ref(v___y_2908_);
lean_dec_ref(v_msg_2906_);
lean_dec_ref(v_tag_2902_);
lean_dec(v_cls_2900_);
v___x_2964_ = lean_st_ref_take(v___y_2909_);
v_traceState_2965_ = lean_ctor_get(v___x_2964_, 4);
v_env_2966_ = lean_ctor_get(v___x_2964_, 0);
v_nextMacroScope_2967_ = lean_ctor_get(v___x_2964_, 1);
v_ngen_2968_ = lean_ctor_get(v___x_2964_, 2);
v_auxDeclNGen_2969_ = lean_ctor_get(v___x_2964_, 3);
v_cache_2970_ = lean_ctor_get(v___x_2964_, 5);
v_messages_2971_ = lean_ctor_get(v___x_2964_, 6);
v_infoState_2972_ = lean_ctor_get(v___x_2964_, 7);
v_snapshotTasks_2973_ = lean_ctor_get(v___x_2964_, 8);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2975_ = v___x_2964_;
v_isShared_2976_ = v_isSharedCheck_2992_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_snapshotTasks_2973_);
lean_inc(v_infoState_2972_);
lean_inc(v_messages_2971_);
lean_inc(v_cache_2970_);
lean_inc(v_traceState_2965_);
lean_inc(v_auxDeclNGen_2969_);
lean_inc(v_ngen_2968_);
lean_inc(v_nextMacroScope_2967_);
lean_inc(v_env_2966_);
lean_dec(v___x_2964_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2992_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
uint64_t v_tid_2977_; lean_object* v_traces_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2991_; 
v_tid_2977_ = lean_ctor_get_uint64(v_traceState_2965_, sizeof(void*)*1);
v_traces_2978_ = lean_ctor_get(v_traceState_2965_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_traceState_2965_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2980_ = v_traceState_2965_;
v_isShared_2981_ = v_isSharedCheck_2991_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_traces_2978_);
lean_dec(v_traceState_2965_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2991_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2982_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2905_, v_traces_2978_);
lean_dec_ref(v_traces_2978_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_2982_);
v___x_2984_ = v___x_2980_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2982_);
lean_ctor_set_uint64(v_reuseFailAlloc_2990_, sizeof(void*)*1, v_tid_2977_);
v___x_2984_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2986_; 
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 4, v___x_2984_);
v___x_2986_ = v___x_2975_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_env_2966_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_nextMacroScope_2967_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_ngen_2968_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v_auxDeclNGen_2969_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_2989_, 5, v_cache_2970_);
lean_ctor_set(v_reuseFailAlloc_2989_, 6, v_messages_2971_);
lean_ctor_set(v_reuseFailAlloc_2989_, 7, v_infoState_2972_);
lean_ctor_set(v_reuseFailAlloc_2989_, 8, v_snapshotTasks_2973_);
v___x_2986_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_st_ref_set(v___y_2909_, v___x_2986_);
lean_dec(v___y_2909_);
v___x_2988_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_fst_2911_);
return v___x_2988_;
}
}
}
}
}
else
{
goto v___jp_2957_;
}
}
else
{
goto v___jp_2957_;
}
}
v___jp_2993_:
{
double v___x_2995_; double v___x_2996_; double v___x_2997_; uint8_t v___x_2998_; 
v___x_2995_ = lean_unbox_float(v_snd_2931_);
v___x_2996_ = lean_unbox_float(v_fst_2930_);
v___x_2997_ = lean_float_sub(v___x_2995_, v___x_2996_);
v___x_2998_ = lean_float_decLt(v___y_2994_, v___x_2997_);
v___y_2963_ = v___x_2998_;
goto v___jp_2962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_3011_, lean_object* v_collapsed_3012_, lean_object* v_tag_3013_, lean_object* v_opts_3014_, lean_object* v_clsEnabled_3015_, lean_object* v_oldTraces_3016_, lean_object* v_msg_3017_, lean_object* v_resStartStop_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
uint8_t v_collapsed_boxed_3022_; uint8_t v_clsEnabled_boxed_3023_; lean_object* v_res_3024_; 
v_collapsed_boxed_3022_ = lean_unbox(v_collapsed_3012_);
v_clsEnabled_boxed_3023_ = lean_unbox(v_clsEnabled_3015_);
v_res_3024_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v_cls_3011_, v_collapsed_boxed_3022_, v_tag_3013_, v_opts_3014_, v_clsEnabled_boxed_3023_, v_oldTraces_3016_, v_msg_3017_, v_resStartStop_3018_, v___y_3019_, v___y_3020_);
lean_dec_ref(v_opts_3014_);
return v_res_3024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3025_ = lean_box(1);
v___x_3026_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3027_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v___x_3026_);
lean_ctor_set(v___x_3028_, 2, v___x_3025_);
return v___x_3028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
lean_ctor_set(v___x_3033_, 3, v___x_3031_);
lean_ctor_set(v___x_3033_, 4, v___x_3031_);
lean_ctor_set(v___x_3033_, 5, v___x_3031_);
lean_ctor_set(v___x_3033_, 6, v___x_3031_);
lean_ctor_set(v___x_3033_, 7, v___x_3031_);
lean_ctor_set(v___x_3033_, 8, v___x_3031_);
return v___x_3033_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3035_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
lean_ctor_set(v___x_3035_, 3, v___x_3034_);
lean_ctor_set(v___x_3035_, 4, v___x_3034_);
lean_ctor_set(v___x_3035_, 5, v___x_3034_);
return v___x_3035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
lean_ctor_set(v___x_3037_, 2, v___x_3036_);
lean_ctor_set(v___x_3037_, 3, v___x_3036_);
lean_ctor_set(v___x_3037_, 4, v___x_3036_);
return v___x_3037_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3038_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3039_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3040_ = lean_box(1);
v___x_3041_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3042_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v___x_3041_);
lean_ctor_set(v___x_3043_, 2, v___x_3040_);
lean_ctor_set(v___x_3043_, 3, v___x_3039_);
lean_ctor_set(v___x_3043_, 4, v___x_3038_);
return v___x_3043_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3047_; double v___x_3048_; 
v___x_3047_ = lean_unsigned_to_nat(1000000000u);
v___x_3048_ = lean_float_of_nat(v___x_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_3049_, lean_object* v_name_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_options_3054_; uint8_t v_hasTrace_3055_; 
v_options_3054_ = lean_ctor_get(v___y_3051_, 2);
v_hasTrace_3055_ = lean_ctor_get_uint8(v_options_3054_, sizeof(void*)*1);
if (v_hasTrace_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v_env_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v___f_3049_);
v___x_3056_ = lean_st_ref_get(v___y_3052_);
v_env_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc_ref(v_env_3057_);
lean_dec(v___x_3056_);
lean_inc(v_name_3050_);
v___x_3058_ = l_Lean_Meta_declFromEqLikeName(v_env_3057_, v_name_3050_);
if (lean_obj_tag(v___x_3058_) == 1)
{
lean_object* v_val_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3148_; 
v_val_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3148_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_val_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3148_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_fst_3063_; lean_object* v_snd_3064_; lean_object* v___x_3065_; lean_object* v_env_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_fst_3063_ = lean_ctor_get(v_val_3059_, 0);
lean_inc(v_fst_3063_);
v_snd_3064_ = lean_ctor_get(v_val_3059_, 1);
lean_inc(v_snd_3064_);
lean_dec(v_val_3059_);
v___x_3065_ = lean_st_ref_get(v___y_3052_);
v_env_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc_ref(v_env_3066_);
lean_dec(v___x_3065_);
lean_inc(v_snd_3064_);
lean_inc(v_fst_3063_);
v___x_3067_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3066_, v_fst_3063_, v_snd_3064_);
v___x_3068_ = lean_name_eq(v_name_3050_, v___x_3067_);
lean_dec(v___x_3067_);
lean_dec(v_name_3050_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
lean_dec(v_snd_3064_);
lean_dec(v_fst_3063_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
v___x_3069_ = lean_box(v_hasTrace_3055_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3069_);
v___x_3071_ = v___x_3061_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
else
{
uint8_t v___x_3073_; lean_object* v_a_3075_; 
lean_inc(v_snd_3064_);
v___x_3073_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3064_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v_a_3092_; 
lean_del_object(v___x_3061_);
v___x_3089_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3090_ = lean_string_dec_eq(v_snd_3064_, v___x_3089_);
lean_dec(v_snd_3064_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec(v_fst_3063_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
v___x_3104_ = lean_box(v_hasTrace_3055_);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3106_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3107_ = lean_box(1);
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3110_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3111_ = lean_box(0);
v___x_3112_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3112_, 0, v___x_3106_);
lean_ctor_set(v___x_3112_, 1, v___x_3107_);
lean_ctor_set(v___x_3112_, 2, v___x_3109_);
lean_ctor_set(v___x_3112_, 3, v___x_3110_);
lean_ctor_set(v___x_3112_, 4, v___x_3111_);
lean_ctor_set(v___x_3112_, 5, v___x_3108_);
lean_ctor_set(v___x_3112_, 6, v___x_3111_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*7, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*7 + 1, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*7 + 2, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*7 + 3, v___x_3068_);
v___x_3113_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3114_ = lean_st_mk_ref(v___x_3113_);
lean_inc(v___x_3114_);
v___x_3115_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3063_, v___x_3068_, v___x_3112_, v___x_3114_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3117_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref(v___x_3115_);
v___x_3117_ = lean_st_ref_get(v___x_3114_);
lean_dec(v___x_3114_);
lean_dec(v___x_3117_);
v_a_3092_ = v_a_3116_;
goto v___jp_3091_;
}
else
{
lean_dec(v___x_3114_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3118_; 
v_a_3118_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3118_);
lean_dec_ref(v___x_3115_);
v_a_3092_ = v_a_3118_;
goto v___jp_3091_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
v_a_3119_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3115_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3115_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
v___jp_3091_:
{
if (lean_obj_tag(v_a_3092_) == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_box(v_hasTrace_3055_);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
else
{
lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3102_; 
v_isSharedCheck_3102_ = !lean_is_exclusive(v_a_3092_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v_a_3092_, 0);
lean_dec(v_unused_3103_);
v___x_3096_ = v_a_3092_;
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
else
{
lean_dec(v_a_3092_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3098_ = lean_box(v___x_3090_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set_tag(v___x_3096_, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec(v_snd_3064_);
v___x_3127_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3128_ = lean_box(1);
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3131_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3133_, 0, v___x_3127_);
lean_ctor_set(v___x_3133_, 1, v___x_3128_);
lean_ctor_set(v___x_3133_, 2, v___x_3130_);
lean_ctor_set(v___x_3133_, 3, v___x_3131_);
lean_ctor_set(v___x_3133_, 4, v___x_3132_);
lean_ctor_set(v___x_3133_, 5, v___x_3129_);
lean_ctor_set(v___x_3133_, 6, v___x_3132_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*7, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*7 + 1, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*7 + 2, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*7 + 3, v___x_3068_);
v___x_3134_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3135_ = lean_st_mk_ref(v___x_3134_);
lean_inc(v___x_3135_);
v___x_3136_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3063_, v___x_3133_, v___x_3135_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3138_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref(v___x_3136_);
v___x_3138_ = lean_st_ref_get(v___x_3135_);
lean_dec(v___x_3135_);
lean_dec(v___x_3138_);
v_a_3075_ = v_a_3137_;
goto v___jp_3074_;
}
else
{
lean_dec(v___x_3135_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3139_; 
v_a_3139_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3139_);
lean_dec_ref(v___x_3136_);
v_a_3075_ = v_a_3139_;
goto v___jp_3074_;
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_del_object(v___x_3061_);
v_a_3140_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3136_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3136_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
v___jp_3074_:
{
if (lean_obj_tag(v_a_3075_) == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_box(v_hasTrace_3055_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3076_);
v___x_3078_ = v___x_3061_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
else
{
lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3087_; 
lean_del_object(v___x_3061_);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_a_3075_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v_a_3075_, 0);
lean_dec(v_unused_3088_);
v___x_3081_ = v_a_3075_;
v_isShared_3082_ = v_isSharedCheck_3087_;
goto v_resetjp_3080_;
}
else
{
lean_dec(v_a_3075_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3087_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3083_ = lean_box(v___x_3073_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3083_);
v___x_3085_ = v___x_3081_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v___x_3058_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v_name_3050_);
v___x_3149_ = lean_box(v_hasTrace_3055_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3430_; 
v___x_3151_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3152_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___x_3151_, v___y_3051_);
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3430_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3430_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v_a_3162_; lean_object* v___y_3176_; lean_object* v___y_3177_; uint8_t v_a_3178_; lean_object* v___y_3182_; lean_object* v___y_3183_; uint8_t v___y_3184_; lean_object* v_a_3185_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v___y_3189_; lean_object* v_a_3190_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v_a_3194_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v_a_3199_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v_a_3212_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; uint8_t v___y_3219_; lean_object* v_a_3220_; lean_object* v___y_3222_; lean_object* v___y_3223_; uint8_t v___y_3224_; lean_object* v_a_3225_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v_a_3230_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; uint8_t v___x_3335_; 
lean_inc(v_name_3050_);
v___f_3157_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3157_, 0, v_name_3050_);
v___x_3158_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1));
v___x_3335_ = lean_unbox(v_a_3153_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; uint8_t v___x_3337_; lean_object* v_a_3339_; lean_object* v_a_3349_; 
v___x_3336_ = l_Lean_trace_profiler;
v___x_3337_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_3054_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3361_; lean_object* v_env_3362_; lean_object* v___x_3363_; 
lean_dec_ref(v___f_3157_);
lean_dec(v_a_3153_);
lean_dec_ref(v___f_3049_);
v___x_3361_ = lean_st_ref_get(v___y_3052_);
v_env_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc_ref(v_env_3362_);
lean_dec(v___x_3361_);
lean_inc(v_name_3050_);
v___x_3363_ = l_Lean_Meta_declFromEqLikeName(v_env_3362_, v_name_3050_);
if (lean_obj_tag(v___x_3363_) == 1)
{
lean_object* v_val_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3427_; 
v_val_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3427_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_val_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3427_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3370_; lean_object* v_env_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_fst_3368_ = lean_ctor_get(v_val_3364_, 0);
lean_inc(v_fst_3368_);
v_snd_3369_ = lean_ctor_get(v_val_3364_, 1);
lean_inc(v_snd_3369_);
lean_dec(v_val_3364_);
v___x_3370_ = lean_st_ref_get(v___y_3052_);
v_env_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc_ref(v_env_3371_);
lean_dec(v___x_3370_);
lean_inc(v_snd_3369_);
lean_inc(v_fst_3368_);
v___x_3372_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3371_, v_fst_3368_, v_snd_3369_);
v___x_3373_ = lean_name_eq(v_name_3050_, v___x_3372_);
lean_dec(v___x_3372_);
lean_dec(v_name_3050_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3376_; 
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3155_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
v___x_3374_ = lean_box(v___x_3337_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3374_);
v___x_3376_ = v___x_3366_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
else
{
uint8_t v___x_3378_; 
lean_inc(v_snd_3369_);
v___x_3378_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3369_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; uint8_t v___x_3380_; 
lean_del_object(v___x_3155_);
v___x_3379_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3380_ = lean_string_dec_eq(v_snd_3369_, v___x_3379_);
lean_dec(v_snd_3369_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_dec(v_fst_3368_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
v___x_3381_ = lean_box(v___x_3337_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3381_);
v___x_3383_ = v___x_3366_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_del_object(v___x_3366_);
v___x_3385_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3386_ = lean_box(1);
v___x_3387_ = lean_unsigned_to_nat(0u);
v___x_3388_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3389_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3391_, 0, v___x_3385_);
lean_ctor_set(v___x_3391_, 1, v___x_3386_);
lean_ctor_set(v___x_3391_, 2, v___x_3388_);
lean_ctor_set(v___x_3391_, 3, v___x_3389_);
lean_ctor_set(v___x_3391_, 4, v___x_3390_);
lean_ctor_set(v___x_3391_, 5, v___x_3387_);
lean_ctor_set(v___x_3391_, 6, v___x_3390_);
lean_ctor_set_uint8(v___x_3391_, sizeof(void*)*7, v___x_3337_);
lean_ctor_set_uint8(v___x_3391_, sizeof(void*)*7 + 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3391_, sizeof(void*)*7 + 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3391_, sizeof(void*)*7 + 3, v_hasTrace_3055_);
v___x_3392_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3393_ = lean_st_mk_ref(v___x_3392_);
lean_inc(v___x_3393_);
v___x_3394_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3368_, v_hasTrace_3055_, v___x_3391_, v___x_3393_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3396_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref(v___x_3394_);
v___x_3396_ = lean_st_ref_get(v___x_3393_);
lean_dec(v___x_3393_);
lean_dec(v___x_3396_);
v_a_3349_ = v_a_3395_;
goto v___jp_3348_;
}
else
{
lean_dec(v___x_3393_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3397_; 
v_a_3397_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___x_3394_);
v_a_3349_ = v_a_3397_;
goto v___jp_3348_;
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
v_a_3398_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3394_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3394_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v_snd_3369_);
lean_del_object(v___x_3366_);
v___x_3406_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3407_ = lean_box(1);
v___x_3408_ = lean_unsigned_to_nat(0u);
v___x_3409_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3410_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3411_ = lean_box(0);
v___x_3412_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3412_, 0, v___x_3406_);
lean_ctor_set(v___x_3412_, 1, v___x_3407_);
lean_ctor_set(v___x_3412_, 2, v___x_3409_);
lean_ctor_set(v___x_3412_, 3, v___x_3410_);
lean_ctor_set(v___x_3412_, 4, v___x_3411_);
lean_ctor_set(v___x_3412_, 5, v___x_3408_);
lean_ctor_set(v___x_3412_, 6, v___x_3411_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*7, v___x_3337_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*7 + 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*7 + 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*7 + 3, v_hasTrace_3055_);
v___x_3413_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3414_ = lean_st_mk_ref(v___x_3413_);
lean_inc(v___x_3414_);
v___x_3415_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3368_, v___x_3412_, v___x_3414_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref(v___x_3415_);
v___x_3417_ = lean_st_ref_get(v___x_3414_);
lean_dec(v___x_3414_);
lean_dec(v___x_3417_);
v_a_3339_ = v_a_3416_;
goto v___jp_3338_;
}
else
{
lean_dec(v___x_3414_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3418_; 
v_a_3418_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3418_);
lean_dec_ref(v___x_3415_);
v_a_3339_ = v_a_3418_;
goto v___jp_3338_;
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_del_object(v___x_3155_);
v_a_3419_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3415_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3415_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
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
lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec(v___x_3363_);
lean_del_object(v___x_3155_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v_name_3050_);
v___x_3428_ = lean_box(v___x_3337_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
else
{
lean_inc_ref(v_options_3054_);
lean_del_object(v___x_3155_);
goto v___jp_3239_;
}
v___jp_3338_:
{
if (lean_obj_tag(v_a_3339_) == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = lean_box(v___x_3337_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3340_);
v___x_3342_ = v___x_3155_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
lean_dec_ref(v_a_3339_);
v___x_3344_ = lean_box(v_hasTrace_3055_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3344_);
v___x_3346_ = v___x_3155_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
v___jp_3348_:
{
if (lean_obj_tag(v_a_3349_) == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = lean_box(v___x_3337_);
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
return v___x_3351_;
}
else
{
lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3359_; 
v_isSharedCheck_3359_ = !lean_is_exclusive(v_a_3349_);
if (v_isSharedCheck_3359_ == 0)
{
lean_object* v_unused_3360_; 
v_unused_3360_ = lean_ctor_get(v_a_3349_, 0);
lean_dec(v_unused_3360_);
v___x_3353_ = v_a_3349_;
v_isShared_3354_ = v_isSharedCheck_3359_;
goto v_resetjp_3352_;
}
else
{
lean_dec(v_a_3349_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3359_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3355_ = lean_box(v_hasTrace_3055_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set_tag(v___x_3353_, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3355_);
v___x_3357_ = v___x_3353_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
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
}
else
{
lean_inc_ref(v_options_3054_);
lean_del_object(v___x_3155_);
goto v___jp_3239_;
}
v___jp_3159_:
{
lean_object* v___x_3163_; double v___x_3164_; double v___x_3165_; double v___x_3166_; double v___x_3167_; double v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; lean_object* v___x_3174_; 
v___x_3163_ = lean_io_mono_nanos_now();
v___x_3164_ = lean_float_of_nat(v___y_3160_);
v___x_3165_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3166_ = lean_float_div(v___x_3164_, v___x_3165_);
v___x_3167_ = lean_float_of_nat(v___x_3163_);
v___x_3168_ = lean_float_div(v___x_3167_, v___x_3165_);
v___x_3169_ = lean_box_float(v___x_3166_);
v___x_3170_ = lean_box_float(v___x_3168_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v_a_3162_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_unbox(v_a_3153_);
lean_dec(v_a_3153_);
v___x_3174_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v___x_3151_, v_hasTrace_3055_, v___x_3158_, v_options_3054_, v___x_3173_, v___y_3161_, v___f_3157_, v___x_3172_, v___y_3051_, v___y_3052_);
lean_dec_ref(v_options_3054_);
return v___x_3174_;
}
v___jp_3175_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_box(v_a_3178_);
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
v___y_3160_ = v___y_3176_;
v___y_3161_ = v___y_3177_;
v_a_3162_ = v___x_3180_;
goto v___jp_3159_;
}
v___jp_3181_:
{
if (lean_obj_tag(v_a_3185_) == 0)
{
v___y_3176_ = v___y_3182_;
v___y_3177_ = v___y_3183_;
v_a_3178_ = v___y_3184_;
goto v___jp_3175_;
}
else
{
lean_dec_ref(v_a_3185_);
v___y_3176_ = v___y_3182_;
v___y_3177_ = v___y_3183_;
v_a_3178_ = v_hasTrace_3055_;
goto v___jp_3175_;
}
}
v___jp_3186_:
{
if (lean_obj_tag(v_a_3190_) == 0)
{
v___y_3176_ = v___y_3187_;
v___y_3177_ = v___y_3188_;
v_a_3178_ = v___y_3189_;
goto v___jp_3175_;
}
else
{
lean_dec_ref(v_a_3190_);
v___y_3176_ = v___y_3187_;
v___y_3177_ = v___y_3188_;
v_a_3178_ = v_hasTrace_3055_;
goto v___jp_3175_;
}
}
v___jp_3191_:
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v_a_3194_);
v___y_3160_ = v___y_3192_;
v___y_3161_ = v___y_3193_;
v_a_3162_ = v___x_3195_;
goto v___jp_3159_;
}
v___jp_3196_:
{
lean_object* v___x_3200_; double v___x_3201_; double v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; lean_object* v___x_3208_; 
v___x_3200_ = lean_io_get_num_heartbeats();
v___x_3201_ = lean_float_of_nat(v___y_3197_);
v___x_3202_ = lean_float_of_nat(v___x_3200_);
v___x_3203_ = lean_box_float(v___x_3201_);
v___x_3204_ = lean_box_float(v___x_3202_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_a_3199_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_unbox(v_a_3153_);
lean_dec(v_a_3153_);
v___x_3208_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v___x_3151_, v_hasTrace_3055_, v___x_3158_, v_options_3054_, v___x_3207_, v___y_3198_, v___f_3157_, v___x_3206_, v___y_3051_, v___y_3052_);
lean_dec_ref(v_options_3054_);
return v___x_3208_;
}
v___jp_3209_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_box(v_a_3212_);
v___x_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
v___y_3197_ = v___y_3210_;
v___y_3198_ = v___y_3211_;
v_a_3199_ = v___x_3214_;
goto v___jp_3196_;
}
v___jp_3215_:
{
if (lean_obj_tag(v_a_3220_) == 0)
{
v___y_3210_ = v___y_3216_;
v___y_3211_ = v___y_3217_;
v_a_3212_ = v___y_3218_;
goto v___jp_3209_;
}
else
{
lean_dec_ref(v_a_3220_);
v___y_3210_ = v___y_3216_;
v___y_3211_ = v___y_3217_;
v_a_3212_ = v___y_3219_;
goto v___jp_3209_;
}
}
v___jp_3221_:
{
if (lean_obj_tag(v_a_3225_) == 0)
{
uint8_t v___x_3226_; 
v___x_3226_ = 0;
v___y_3210_ = v___y_3222_;
v___y_3211_ = v___y_3223_;
v_a_3212_ = v___x_3226_;
goto v___jp_3209_;
}
else
{
lean_dec_ref(v_a_3225_);
v___y_3210_ = v___y_3222_;
v___y_3211_ = v___y_3223_;
v_a_3212_ = v___y_3224_;
goto v___jp_3209_;
}
}
v___jp_3227_:
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_a_3230_);
v___y_3197_ = v___y_3228_;
v___y_3198_ = v___y_3229_;
v_a_3199_ = v___x_3231_;
goto v___jp_3196_;
}
v___jp_3232_:
{
if (lean_obj_tag(v___y_3235_) == 0)
{
lean_object* v_a_3236_; uint8_t v___x_3237_; 
v_a_3236_ = lean_ctor_get(v___y_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref(v___y_3235_);
v___x_3237_ = lean_unbox(v_a_3236_);
lean_dec(v_a_3236_);
v___y_3210_ = v___y_3233_;
v___y_3211_ = v___y_3234_;
v_a_3212_ = v___x_3237_;
goto v___jp_3209_;
}
else
{
lean_object* v_a_3238_; 
v_a_3238_ = lean_ctor_get(v___y_3235_, 0);
lean_inc(v_a_3238_);
lean_dec_ref(v___y_3235_);
v___y_3228_ = v___y_3233_;
v___y_3229_ = v___y_3234_;
v_a_3230_ = v_a_3238_;
goto v___jp_3227_;
}
}
v___jp_3239_:
{
lean_object* v___x_3240_; lean_object* v_a_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3240_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_3052_);
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref(v___x_3240_);
v___x_3242_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3243_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_3054_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v_env_3246_; lean_object* v___x_3247_; 
lean_dec_ref(v___f_3049_);
v___x_3244_ = lean_io_mono_nanos_now();
v___x_3245_ = lean_st_ref_get(v___y_3052_);
v_env_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc_ref(v_env_3246_);
lean_dec(v___x_3245_);
lean_inc(v_name_3050_);
v___x_3247_ = l_Lean_Meta_declFromEqLikeName(v_env_3246_, v_name_3050_);
if (lean_obj_tag(v___x_3247_) == 1)
{
lean_object* v_val_3248_; lean_object* v_fst_3249_; lean_object* v_snd_3250_; lean_object* v___x_3251_; lean_object* v_env_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v_val_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_val_3248_);
lean_dec_ref(v___x_3247_);
v_fst_3249_ = lean_ctor_get(v_val_3248_, 0);
lean_inc(v_fst_3249_);
v_snd_3250_ = lean_ctor_get(v_val_3248_, 1);
lean_inc(v_snd_3250_);
lean_dec(v_val_3248_);
v___x_3251_ = lean_st_ref_get(v___y_3052_);
v_env_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc_ref(v_env_3252_);
lean_dec(v___x_3251_);
lean_inc(v_snd_3250_);
lean_inc(v_fst_3249_);
v___x_3253_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3252_, v_fst_3249_, v_snd_3250_);
v___x_3254_ = lean_name_eq(v_name_3050_, v___x_3253_);
lean_dec(v___x_3253_);
lean_dec(v_name_3050_);
if (v___x_3254_ == 0)
{
lean_dec(v_snd_3250_);
lean_dec(v_fst_3249_);
v___y_3176_ = v___x_3244_;
v___y_3177_ = v_a_3241_;
v_a_3178_ = v___x_3243_;
goto v___jp_3175_;
}
else
{
uint8_t v___x_3255_; 
lean_inc(v_snd_3250_);
v___x_3255_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3250_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3256_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3257_ = lean_string_dec_eq(v_snd_3250_, v___x_3256_);
lean_dec(v_snd_3250_);
if (v___x_3257_ == 0)
{
lean_dec(v_fst_3249_);
v___y_3176_ = v___x_3244_;
v___y_3177_ = v_a_3241_;
v_a_3178_ = v___x_3243_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3258_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3259_ = lean_box(1);
v___x_3260_ = lean_unsigned_to_nat(0u);
v___x_3261_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3262_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3263_ = lean_box(0);
v___x_3264_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3264_, 0, v___x_3258_);
lean_ctor_set(v___x_3264_, 1, v___x_3259_);
lean_ctor_set(v___x_3264_, 2, v___x_3261_);
lean_ctor_set(v___x_3264_, 3, v___x_3262_);
lean_ctor_set(v___x_3264_, 4, v___x_3263_);
lean_ctor_set(v___x_3264_, 5, v___x_3260_);
lean_ctor_set(v___x_3264_, 6, v___x_3263_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7, v___x_3243_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 1, v___x_3243_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 2, v___x_3243_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 3, v_hasTrace_3055_);
v___x_3265_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3266_ = lean_st_mk_ref(v___x_3265_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
lean_inc(v___x_3266_);
v___x_3267_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3249_, v_hasTrace_3055_, v___x_3264_, v___x_3266_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3269_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
lean_dec_ref(v___x_3267_);
v___x_3269_ = lean_st_ref_get(v___x_3266_);
lean_dec(v___x_3266_);
lean_dec(v___x_3269_);
v___y_3187_ = v___x_3244_;
v___y_3188_ = v_a_3241_;
v___y_3189_ = v___x_3243_;
v_a_3190_ = v_a_3268_;
goto v___jp_3186_;
}
else
{
lean_dec(v___x_3266_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3267_);
v___y_3187_ = v___x_3244_;
v___y_3188_ = v_a_3241_;
v___y_3189_ = v___x_3243_;
v_a_3190_ = v_a_3270_;
goto v___jp_3186_;
}
else
{
lean_object* v_a_3271_; 
v_a_3271_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3271_);
lean_dec_ref(v___x_3267_);
v___y_3192_ = v___x_3244_;
v___y_3193_ = v_a_3241_;
v_a_3194_ = v_a_3271_;
goto v___jp_3191_;
}
}
}
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec(v_snd_3250_);
v___x_3272_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3273_ = lean_box(1);
v___x_3274_ = lean_unsigned_to_nat(0u);
v___x_3275_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3276_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3277_ = lean_box(0);
v___x_3278_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3278_, 0, v___x_3272_);
lean_ctor_set(v___x_3278_, 1, v___x_3273_);
lean_ctor_set(v___x_3278_, 2, v___x_3275_);
lean_ctor_set(v___x_3278_, 3, v___x_3276_);
lean_ctor_set(v___x_3278_, 4, v___x_3277_);
lean_ctor_set(v___x_3278_, 5, v___x_3274_);
lean_ctor_set(v___x_3278_, 6, v___x_3277_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7, v___x_3243_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 1, v___x_3243_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 2, v___x_3243_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 3, v_hasTrace_3055_);
v___x_3279_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3280_ = lean_st_mk_ref(v___x_3279_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
lean_inc(v___x_3280_);
v___x_3281_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3249_, v___x_3278_, v___x_3280_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3283_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = lean_st_ref_get(v___x_3280_);
lean_dec(v___x_3280_);
lean_dec(v___x_3283_);
v___y_3182_ = v___x_3244_;
v___y_3183_ = v_a_3241_;
v___y_3184_ = v___x_3243_;
v_a_3185_ = v_a_3282_;
goto v___jp_3181_;
}
else
{
lean_dec(v___x_3280_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3284_; 
v_a_3284_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3284_);
lean_dec_ref(v___x_3281_);
v___y_3182_ = v___x_3244_;
v___y_3183_ = v_a_3241_;
v___y_3184_ = v___x_3243_;
v_a_3185_ = v_a_3284_;
goto v___jp_3181_;
}
else
{
lean_object* v_a_3285_; 
v_a_3285_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3285_);
lean_dec_ref(v___x_3281_);
v___y_3192_ = v___x_3244_;
v___y_3193_ = v_a_3241_;
v_a_3194_ = v_a_3285_;
goto v___jp_3191_;
}
}
}
}
}
else
{
lean_dec(v___x_3247_);
lean_dec(v_name_3050_);
v___y_3176_ = v___x_3244_;
v___y_3177_ = v_a_3241_;
v_a_3178_ = v___x_3243_;
goto v___jp_3175_;
}
}
else
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v_env_3288_; lean_object* v___x_3289_; 
v___x_3286_ = lean_io_get_num_heartbeats();
v___x_3287_ = lean_st_ref_get(v___y_3052_);
v_env_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc_ref(v_env_3288_);
lean_dec(v___x_3287_);
lean_inc(v_name_3050_);
v___x_3289_ = l_Lean_Meta_declFromEqLikeName(v_env_3288_, v_name_3050_);
if (lean_obj_tag(v___x_3289_) == 1)
{
lean_object* v_val_3290_; lean_object* v_fst_3291_; lean_object* v_snd_3292_; lean_object* v___x_3293_; lean_object* v_env_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_val_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_val_3290_);
lean_dec_ref(v___x_3289_);
v_fst_3291_ = lean_ctor_get(v_val_3290_, 0);
lean_inc(v_fst_3291_);
v_snd_3292_ = lean_ctor_get(v_val_3290_, 1);
lean_inc(v_snd_3292_);
lean_dec(v_val_3290_);
v___x_3293_ = lean_st_ref_get(v___y_3052_);
v_env_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc_ref(v_env_3294_);
lean_dec(v___x_3293_);
lean_inc(v_snd_3292_);
lean_inc(v_fst_3291_);
v___x_3295_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3294_, v_fst_3291_, v_snd_3292_);
v___x_3296_ = lean_name_eq(v_name_3050_, v___x_3295_);
lean_dec(v___x_3295_);
lean_dec(v_name_3050_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec(v_snd_3292_);
lean_dec(v_fst_3291_);
v___x_3297_ = lean_box(0);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3298_ = lean_apply_4(v___f_3049_, v___x_3297_, v___y_3051_, v___y_3052_, lean_box(0));
v___y_3233_ = v___x_3286_;
v___y_3234_ = v_a_3241_;
v___y_3235_ = v___x_3298_;
goto v___jp_3232_;
}
else
{
uint8_t v___x_3299_; 
lean_inc(v_snd_3292_);
v___x_3299_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3292_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; uint8_t v___x_3301_; 
v___x_3300_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3301_ = lean_string_dec_eq(v_snd_3292_, v___x_3300_);
lean_dec(v_snd_3292_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec(v_fst_3291_);
v___x_3302_ = lean_box(0);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3303_ = lean_apply_4(v___f_3049_, v___x_3302_, v___y_3051_, v___y_3052_, lean_box(0));
v___y_3233_ = v___x_3286_;
v___y_3234_ = v_a_3241_;
v___y_3235_ = v___x_3303_;
goto v___jp_3232_;
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec_ref(v___f_3049_);
v___x_3304_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3305_ = lean_box(1);
v___x_3306_ = lean_unsigned_to_nat(0u);
v___x_3307_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3309_ = lean_box(0);
v___x_3310_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3310_, 0, v___x_3304_);
lean_ctor_set(v___x_3310_, 1, v___x_3305_);
lean_ctor_set(v___x_3310_, 2, v___x_3307_);
lean_ctor_set(v___x_3310_, 3, v___x_3308_);
lean_ctor_set(v___x_3310_, 4, v___x_3309_);
lean_ctor_set(v___x_3310_, 5, v___x_3306_);
lean_ctor_set(v___x_3310_, 6, v___x_3309_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7, v___x_3299_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 1, v___x_3299_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 2, v___x_3299_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 3, v___x_3243_);
v___x_3311_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3312_ = lean_st_mk_ref(v___x_3311_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
lean_inc(v___x_3312_);
v___x_3313_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3291_, v___x_3243_, v___x_3310_, v___x_3312_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref(v___x_3313_);
v___x_3315_ = lean_st_ref_get(v___x_3312_);
lean_dec(v___x_3312_);
lean_dec(v___x_3315_);
v___y_3216_ = v___x_3286_;
v___y_3217_ = v_a_3241_;
v___y_3218_ = v___x_3299_;
v___y_3219_ = v___x_3243_;
v_a_3220_ = v_a_3314_;
goto v___jp_3215_;
}
else
{
lean_dec(v___x_3312_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3316_; 
v_a_3316_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3316_);
lean_dec_ref(v___x_3313_);
v___y_3216_ = v___x_3286_;
v___y_3217_ = v_a_3241_;
v___y_3218_ = v___x_3299_;
v___y_3219_ = v___x_3243_;
v_a_3220_ = v_a_3316_;
goto v___jp_3215_;
}
else
{
lean_object* v_a_3317_; 
v_a_3317_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3313_);
v___y_3228_ = v___x_3286_;
v___y_3229_ = v_a_3241_;
v_a_3230_ = v_a_3317_;
goto v___jp_3227_;
}
}
}
}
else
{
lean_object* v___x_3318_; uint8_t v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec(v_snd_3292_);
lean_dec_ref(v___f_3049_);
v___x_3318_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3319_ = 0;
v___x_3320_ = lean_box(1);
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3323_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3325_, 0, v___x_3318_);
lean_ctor_set(v___x_3325_, 1, v___x_3320_);
lean_ctor_set(v___x_3325_, 2, v___x_3322_);
lean_ctor_set(v___x_3325_, 3, v___x_3323_);
lean_ctor_set(v___x_3325_, 4, v___x_3324_);
lean_ctor_set(v___x_3325_, 5, v___x_3321_);
lean_ctor_set(v___x_3325_, 6, v___x_3324_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*7, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*7 + 1, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*7 + 2, v___x_3319_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*7 + 3, v___x_3243_);
v___x_3326_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3327_ = lean_st_mk_ref(v___x_3326_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
lean_inc(v___x_3327_);
v___x_3328_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3291_, v___x_3325_, v___x_3327_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = lean_st_ref_get(v___x_3327_);
lean_dec(v___x_3327_);
lean_dec(v___x_3330_);
v___y_3222_ = v___x_3286_;
v___y_3223_ = v_a_3241_;
v___y_3224_ = v___x_3243_;
v_a_3225_ = v_a_3329_;
goto v___jp_3221_;
}
else
{
lean_dec(v___x_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3331_; 
v_a_3331_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3331_);
lean_dec_ref(v___x_3328_);
v___y_3222_ = v___x_3286_;
v___y_3223_ = v_a_3241_;
v___y_3224_ = v___x_3243_;
v_a_3225_ = v_a_3331_;
goto v___jp_3221_;
}
else
{
lean_object* v_a_3332_; 
v_a_3332_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3328_);
v___y_3228_ = v___x_3286_;
v___y_3229_ = v_a_3241_;
v_a_3230_ = v_a_3332_;
goto v___jp_3227_;
}
}
}
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec(v___x_3289_);
lean_dec(v_name_3050_);
v___x_3333_ = lean_box(0);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3334_ = lean_apply_4(v___f_3049_, v___x_3333_, v___y_3051_, v___y_3052_, lean_box(0));
v___y_3233_ = v___x_3286_;
v___y_3234_ = v_a_3241_;
v___y_3235_ = v___x_3334_;
goto v___jp_3232_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3431_, lean_object* v_name_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3431_, v_name_3432_, v___y_3433_, v___y_3434_);
return v_res_3436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = lean_unsigned_to_nat(3137104340u);
v___x_3481_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3482_ = l_Lean_Name_num___override(v___x_3481_, v___x_3480_);
return v___x_3482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3485_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3486_ = l_Lean_Name_str___override(v___x_3485_, v___x_3484_);
return v___x_3486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3489_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3490_ = l_Lean_Name_str___override(v___x_3489_, v___x_3488_);
return v___x_3490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3491_ = lean_unsigned_to_nat(2u);
v___x_3492_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3493_ = l_Lean_Name_num___override(v___x_3492_, v___x_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3495_; lean_object* v___x_3496_; 
v___f_3495_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3496_ = l_Lean_registerReservedNameAction(v___f_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v___x_3497_; uint8_t v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_dec_ref(v___x_3496_);
v___x_3497_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_3498_ = 0;
v___x_3499_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3500_ = l_Lean_registerTraceClass(v___x_3497_, v___x_3498_, v___x_3499_);
return v___x_3500_;
}
else
{
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_00_u03b1_3503_, lean_object* v_x_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_x_3504_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_00_u03b1_3509_, lean_object* v_x_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4(v_00_u03b1_3509_, v_x_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
return v_res_3514_;
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
