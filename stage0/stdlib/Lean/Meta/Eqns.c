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
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_isEqnReservedNameSuffix___closed__0;
static const lean_ctor_object l_Lean_Meta_isEqnReservedNameSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_isEqnReservedNameSuffix___closed__1 = (const lean_object*)&l_Lean_Meta_isEqnReservedNameSuffix___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(lean_object* v___x_102_, lean_object* v___x_103_, lean_object* v_s_104_, lean_object* v_a_105_, lean_object* v_b_106_){
_start:
{
lean_object* v_startInclusive_107_; lean_object* v_endExclusive_108_; lean_object* v___x_109_; uint8_t v_lastWasDigit_110_; 
v_startInclusive_107_ = lean_ctor_get(v___x_102_, 1);
v_endExclusive_108_ = lean_ctor_get(v___x_102_, 2);
v___x_109_ = lean_nat_sub(v_endExclusive_108_, v_startInclusive_107_);
v_lastWasDigit_110_ = lean_nat_dec_eq(v_a_105_, v___x_109_);
lean_dec(v___x_109_);
if (v_lastWasDigit_110_ == 0)
{
lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_145_; 
v_snd_111_ = lean_ctor_get(v_b_106_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_b_106_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v_b_106_, 0);
lean_dec(v_unused_146_);
v___x_113_ = v_b_106_;
v_isShared_114_ = v_isSharedCheck_145_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_dec(v_b_106_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_145_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___y_120_; uint32_t v___x_131_; uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_115_ = lean_box(0);
v___x_116_ = lean_nat_add(v___x_103_, v_a_105_);
lean_dec(v_a_105_);
v___x_117_ = lean_string_utf8_next_fast(v_s_104_, v___x_116_);
v___x_118_ = lean_nat_sub(v___x_117_, v___x_103_);
v___x_131_ = lean_string_utf8_get_fast(v_s_104_, v___x_116_);
lean_dec(v___x_116_);
v___x_132_ = 95;
v___x_133_ = lean_uint32_dec_eq(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 48;
v___x_135_ = lean_uint32_dec_le(v___x_134_, v___x_131_);
if (v___x_135_ == 0)
{
v___y_120_ = v___x_135_;
goto v___jp_119_;
}
else
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 57;
v___x_137_ = lean_uint32_dec_le(v___x_131_, v___x_136_);
v___y_120_ = v___x_137_;
goto v___jp_119_;
}
}
else
{
uint8_t v___x_138_; 
lean_del_object(v___x_113_);
v___x_138_ = lean_unbox(v_snd_111_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v___x_118_);
v___x_139_ = lean_box(v_lastWasDigit_110_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_snd_111_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_snd_111_);
v___x_142_ = lean_box(v_lastWasDigit_110_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_115_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v_a_105_ = v___x_118_;
v_b_106_ = v___x_143_;
goto _start;
}
}
v___jp_119_:
{
if (v___y_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
lean_dec(v___x_118_);
v___x_121_ = lean_box(v_lastWasDigit_110_);
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_122_);
v___x_124_ = v___x_113_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_snd_111_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_128_; 
lean_dec(v_snd_111_);
v___x_126_ = lean_box(v___y_120_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_126_);
lean_ctor_set(v___x_113_, 0, v___x_115_);
v___x_128_ = v___x_113_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_130_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
v_a_105_ = v___x_118_;
v_b_106_ = v___x_128_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_105_);
return v_b_106_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg___boxed(lean_object* v___x_147_, lean_object* v___x_148_, lean_object* v_s_149_, lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(v___x_147_, v___x_148_, v_s_149_, v_a_150_, v_b_151_);
lean_dec_ref(v_s_149_);
lean_dec(v___x_148_);
lean_dec_ref(v___x_147_);
return v_res_152_;
}
}
static lean_object* _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_154_ = lean_string_utf8_byte_size(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_160_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_161_ = lean_string_utf8_byte_size(v_s_159_);
v___x_162_ = lean_obj_once(&l_Lean_Meta_isEqnReservedNameSuffix___closed__0, &l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0);
v___x_163_ = lean_nat_dec_le(v___x_162_, v___x_161_);
if (v___x_163_ == 0)
{
lean_dec_ref(v_s_159_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_string_memcmp(v_s_159_, v___x_160_, v___x_164_, v___x_164_, v___x_162_);
if (v___x_165_ == 0)
{
lean_dec_ref(v_s_159_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_fst_173_; 
v___x_166_ = lean_unsigned_to_nat(3u);
lean_inc_ref(v_s_159_);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v_s_159_);
lean_ctor_set(v___x_167_, 1, v___x_164_);
lean_ctor_set(v___x_167_, 2, v___x_161_);
v___x_168_ = l_String_Slice_Pos_nextn(v___x_167_, v___x_164_, v___x_166_);
lean_dec_ref(v___x_167_);
lean_inc(v___x_168_);
lean_inc_ref(v_s_159_);
v___x_169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_169_, 0, v_s_159_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
lean_ctor_set(v___x_169_, 2, v___x_161_);
v___x_170_ = ((lean_object*)(l_Lean_Meta_isEqnReservedNameSuffix___closed__1));
v___x_171_ = l_String_Slice_positions(v___x_169_);
v___x_172_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(v___x_169_, v___x_168_, v_s_159_, v___x_171_, v___x_170_);
lean_dec_ref(v_s_159_);
lean_dec(v___x_168_);
lean_dec_ref(v___x_169_);
v_fst_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_fst_173_);
if (lean_obj_tag(v_fst_173_) == 0)
{
lean_object* v_snd_174_; uint8_t v___x_175_; 
v_snd_174_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_snd_174_);
lean_dec_ref(v___x_172_);
v___x_175_ = lean_unbox(v_snd_174_);
lean_dec(v_snd_174_);
return v___x_175_;
}
else
{
lean_object* v_val_176_; uint8_t v___x_177_; 
lean_dec_ref(v___x_172_);
v_val_176_ = lean_ctor_get(v_fst_173_, 0);
lean_inc(v_val_176_);
lean_dec_ref(v_fst_173_);
v___x_177_ = lean_unbox(v_val_176_);
lean_dec(v_val_176_);
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0(lean_object* v___x_181_, lean_object* v___x_182_, lean_object* v_s_183_, lean_object* v_inst_184_, lean_object* v_R_185_, lean_object* v_a_186_, lean_object* v_b_187_, lean_object* v_c_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___redArg(v___x_181_, v___x_182_, v_s_183_, v_a_186_, v_b_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0___boxed(lean_object* v___x_190_, lean_object* v___x_191_, lean_object* v_s_192_, lean_object* v_inst_193_, lean_object* v_R_194_, lean_object* v_a_195_, lean_object* v_b_196_, lean_object* v_c_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_isEqnReservedNameSuffix_spec__0(v___x_190_, v___x_191_, v_s_192_, v_inst_193_, v_R_194_, v_a_195_, v_b_196_, v_c_197_);
lean_dec_ref(v_s_192_);
lean_dec(v___x_191_);
lean_dec_ref(v___x_190_);
return v_res_198_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_203_){
_start:
{
uint8_t v___y_205_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_208_ = lean_string_dec_eq(v_s_203_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_210_ = lean_string_dec_eq(v_s_203_, v___x_209_);
v___y_205_ = v___x_210_;
goto v___jp_204_;
}
else
{
v___y_205_ = v___x_208_;
goto v___jp_204_;
}
v___jp_204_:
{
if (v___y_205_ == 0)
{
uint8_t v___x_206_; 
v___x_206_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_203_);
return v___x_206_;
}
else
{
lean_dec_ref(v_s_203_);
return v___y_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Lean_Meta_isEqnLikeSuffix(v_s_211_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_217_, lean_object* v_env_218_, lean_object* v_as_x27_219_, lean_object* v_b_220_){
_start:
{
if (lean_obj_tag(v_as_x27_219_) == 0)
{
lean_dec_ref(v_env_218_);
lean_dec_ref(v_str_217_);
return v_b_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_b_220_);
v_head_221_ = lean_ctor_get(v_as_x27_219_, 0);
v_tail_222_ = lean_ctor_get(v_as_x27_219_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_as_x27_219_);
if (v_isSharedCheck_242_ == 0)
{
v___x_224_ = v_as_x27_219_;
v_isShared_225_ = v_isSharedCheck_242_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_head_221_);
lean_dec(v_as_x27_219_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_242_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___y_229_; uint8_t v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_226_ = lean_box(0);
v___x_227_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_237_ = 0;
lean_inc_ref(v_env_218_);
v___x_238_ = l_Lean_Environment_setExporting(v_env_218_, v___x_237_);
lean_inc(v_head_221_);
v___x_239_ = l_Lean_Environment_isSafeDefinition(v___x_238_, v_head_221_);
if (v___x_239_ == 0)
{
v___y_229_ = v___x_239_;
goto v___jp_228_;
}
else
{
uint8_t v___x_240_; 
lean_inc(v_head_221_);
lean_inc_ref(v_env_218_);
v___x_240_ = lean_is_matcher(v_env_218_, v_head_221_);
if (v___x_240_ == 0)
{
v___y_229_ = v___x_239_;
goto v___jp_228_;
}
else
{
lean_del_object(v___x_224_);
lean_dec(v_head_221_);
v_as_x27_219_ = v_tail_222_;
v_b_220_ = v___x_227_;
goto _start;
}
}
v___jp_228_:
{
if (v___y_229_ == 0)
{
lean_del_object(v___x_224_);
lean_dec(v_head_221_);
v_as_x27_219_ = v_tail_222_;
v_b_220_ = v___x_227_;
goto _start;
}
else
{
lean_object* v___x_232_; 
lean_dec(v_tail_222_);
lean_dec_ref(v_env_218_);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 0);
lean_ctor_set(v___x_224_, 1, v_str_217_);
v___x_232_ = v___x_224_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_head_221_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_str_217_);
v___x_232_ = v_reuseFailAlloc_236_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_226_);
return v___x_235_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_243_, lean_object* v_name_244_){
_start:
{
if (lean_obj_tag(v_name_244_) == 1)
{
lean_object* v_pre_245_; lean_object* v_str_246_; uint8_t v___x_247_; 
v_pre_245_ = lean_ctor_get(v_name_244_, 0);
lean_inc(v_pre_245_);
v_str_246_ = lean_ctor_get(v_name_244_, 1);
lean_inc_ref(v_str_246_);
lean_dec_ref(v_name_244_);
lean_inc_ref(v_str_246_);
v___x_247_ = l_Lean_Meta_isEqnLikeSuffix(v_str_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec_ref(v_str_246_);
lean_dec(v_pre_245_);
lean_dec_ref(v_env_243_);
v___x_248_ = lean_box(0);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_fst_256_; 
lean_inc(v_pre_245_);
v___x_249_ = l_Lean_privateToUserName(v_pre_245_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v_pre_245_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_box(0);
v___x_254_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_255_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_246_, v_env_243_, v___x_252_, v___x_254_);
v_fst_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_fst_256_);
lean_dec_ref(v___x_255_);
if (lean_obj_tag(v_fst_256_) == 0)
{
return v___x_253_;
}
else
{
lean_object* v_val_257_; 
v_val_257_ = lean_ctor_get(v_fst_256_, 0);
lean_inc(v_val_257_);
lean_dec_ref(v_fst_256_);
return v_val_257_;
}
}
}
else
{
lean_object* v___x_258_; 
lean_dec(v_name_244_);
lean_dec_ref(v_env_243_);
v___x_258_ = lean_box(0);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_259_, lean_object* v_env_260_, lean_object* v_as_261_, lean_object* v_as_x27_262_, lean_object* v_b_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_259_, v_env_260_, v_as_x27_262_, v_b_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_266_, lean_object* v_env_267_, lean_object* v_as_268_, lean_object* v_as_x27_269_, lean_object* v_b_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_266_, v_env_267_, v_as_268_, v_as_x27_269_, v_b_270_, v_a_271_);
lean_dec(v_as_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_273_, lean_object* v_declName_274_, lean_object* v_suffix_275_){
_start:
{
lean_object* v___x_279_; uint8_t v_isModule_280_; 
v___x_279_ = l_Lean_Environment_header(v_env_273_);
v_isModule_280_ = lean_ctor_get_uint8(v___x_279_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_279_);
if (v_isModule_280_ == 0)
{
lean_object* v_name_281_; 
lean_dec_ref(v_env_273_);
v_name_281_ = l_Lean_Name_str___override(v_declName_274_, v_suffix_275_);
return v_name_281_;
}
else
{
uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = 0;
lean_inc_ref(v_env_273_);
v___x_283_ = l_Lean_Environment_setExporting(v_env_273_, v_isModule_280_);
lean_inc(v_declName_274_);
v___x_284_ = l_Lean_Environment_find_x3f(v___x_283_, v_declName_274_, v___x_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
goto v___jp_276_;
}
else
{
lean_object* v_val_285_; uint8_t v___x_286_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref(v___x_284_);
v___x_286_ = l_Lean_ConstantInfo_hasValue(v_val_285_, v___x_282_);
lean_dec(v_val_285_);
if (v___x_286_ == 0)
{
goto v___jp_276_;
}
else
{
lean_object* v_name_287_; 
lean_dec_ref(v_env_273_);
v_name_287_ = l_Lean_Name_str___override(v_declName_274_, v_suffix_275_);
return v_name_287_;
}
}
}
v___jp_276_:
{
lean_object* v_name_277_; lean_object* v___x_278_; 
v_name_277_ = l_Lean_Name_str___override(v_declName_274_, v_suffix_275_);
v___x_278_ = l_Lean_mkPrivateName(v_env_273_, v_name_277_);
lean_dec_ref(v_env_273_);
return v___x_278_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_288_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
lean_ctor_set(v___x_293_, 3, v___x_291_);
lean_ctor_set(v___x_293_, 4, v___x_291_);
lean_ctor_set(v___x_293_, 5, v___x_291_);
lean_ctor_set(v___x_293_, 6, v___x_291_);
lean_ctor_set(v___x_293_, 7, v___x_291_);
lean_ctor_set(v___x_293_, 8, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(32u);
v___x_295_ = lean_mk_empty_array_with_capacity(v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_297_ = ((size_t)5ULL);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_unsigned_to_nat(32u);
v___x_300_ = lean_mk_empty_array_with_capacity(v___x_299_);
v___x_301_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_302_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_298_);
lean_ctor_set(v___x_302_, 3, v___x_298_);
lean_ctor_set_usize(v___x_302_, 4, v___x_297_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_box(1);
v___x_304_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_305_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v_options_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_311_ = lean_st_ref_get(v___y_309_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_env_312_);
lean_dec(v___x_311_);
v_options_313_ = lean_ctor_get(v___y_308_, 2);
v___x_314_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_313_);
v___x_316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_316_, 0, v_env_312_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_315_);
lean_ctor_set(v___x_316_, 3, v_options_313_);
v___x_317_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_msgData_307_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_ref_328_; lean_object* v___x_329_; lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
v_ref_328_ = lean_ctor_get(v___y_325_, 5);
v___x_329_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_324_, v___y_325_, v___y_326_);
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_338_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
lean_inc(v_ref_328_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_ref_328_);
lean_ctor_set(v___x_334_, 1, v_a_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_336_ = v___x_332_;
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
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_343_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_346_ = l_Lean_stringToMessageData(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_349_ = l_Lean_stringToMessageData(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_353_, lean_object* v_reservedName_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_358_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_359_ = 0;
v___x_360_ = l_Lean_MessageData_ofConstName(v_declName_353_, v___x_359_);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_358_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = 1;
v___x_365_ = l_Lean_MessageData_ofConstName(v_reservedName_354_, v___x_364_);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_363_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_368_, v___y_355_, v___y_356_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_370_, lean_object* v_reservedName_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_370_, v_reservedName_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_376_, lean_object* v_suffix_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_env_382_; lean_object* v_reservedName_383_; uint8_t v___x_384_; uint8_t v___x_385_; 
v___x_381_ = lean_st_ref_get(v___y_379_);
v_env_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_env_382_);
lean_dec(v___x_381_);
lean_inc(v_declName_376_);
v_reservedName_383_ = l_Lean_Name_str___override(v_declName_376_, v_suffix_377_);
v___x_384_ = 1;
lean_inc(v_reservedName_383_);
v___x_385_ = l_Lean_Environment_contains(v_env_382_, v_reservedName_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_reservedName_383_);
lean_dec(v_declName_376_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_376_, v_reservedName_383_, v___y_378_, v___y_379_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_389_, lean_object* v_suffix_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_389_, v_suffix_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_395_);
v___x_400_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_395_, v___x_399_, v_a_396_, v_a_397_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref(v___x_400_);
v___x_401_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_395_);
v___x_402_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_395_, v___x_401_, v_a_396_, v_a_397_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref(v___x_402_);
v___x_403_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_404_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_395_, v___x_403_, v_a_396_, v_a_397_);
return v___x_404_;
}
else
{
lean_dec(v_declName_395_);
return v___x_402_;
}
}
else
{
lean_dec(v_declName_395_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_411_, v___y_412_, v___y_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_416_, v_msg_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_421_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_422_, lean_object* v_n_423_){
_start:
{
lean_object* v___x_424_; 
lean_inc(v_n_423_);
lean_inc_ref(v_env_422_);
v___x_424_ = l_Lean_Meta_declFromEqLikeName(v_env_422_, v_n_423_);
if (lean_obj_tag(v___x_424_) == 1)
{
lean_object* v_val_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_val_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_425_);
lean_dec_ref(v___x_424_);
v_fst_426_ = lean_ctor_get(v_val_425_, 0);
lean_inc(v_fst_426_);
v_snd_427_ = lean_ctor_get(v_val_425_, 1);
lean_inc(v_snd_427_);
lean_dec(v_val_425_);
v___x_428_ = l_Lean_Meta_mkEqLikeNameFor(v_env_422_, v_fst_426_, v_snd_427_);
v___x_429_ = lean_name_eq(v_n_423_, v___x_428_);
lean_dec(v___x_428_);
lean_dec(v_n_423_);
return v___x_429_;
}
else
{
uint8_t v___x_430_; 
lean_dec(v___x_424_);
lean_dec(v_n_423_);
lean_dec_ref(v_env_422_);
v___x_430_ = 0;
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_431_, lean_object* v_n_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_431_, v_n_432_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_437_; lean_object* v___x_438_; 
v___f_437_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_438_ = l_Lean_registerReservedNamePredicate(v___f_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
v___x_443_ = lean_st_mk_ref(v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_446_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_449_ = lean_mk_io_user_error(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_initializing();
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_469_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_469_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_469_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_469_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
uint8_t v___x_457_; 
v___x_457_ = lean_unbox(v_a_453_);
lean_dec(v_a_453_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec_ref(v_f_450_);
v___x_458_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 1);
lean_ctor_set(v___x_455_, 0, v___x_458_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_462_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_463_ = lean_st_ref_take(v___x_462_);
v___x_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_464_, 0, v_f_450_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_st_ref_set(v___x_462_, v___x_464_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_465_);
v___x_467_ = v___x_455_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v_f_450_);
v_a_470_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_452_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_452_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_registerGetEqnsFn(v_f_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_491_; lean_object* v_env_492_; uint8_t v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_st_ref_get(v_a_485_);
v_env_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_env_492_);
lean_dec(v___x_491_);
v___x_493_ = 0;
lean_inc(v_declName_481_);
v___x_494_ = l_Lean_Environment_findAsync_x3f(v_env_492_, v_declName_481_, v___x_493_);
if (lean_obj_tag(v___x_494_) == 1)
{
lean_object* v_val_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_526_; 
v_val_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_526_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_526_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_val_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_526_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v_kind_499_; 
v_kind_499_ = lean_ctor_get_uint8(v_val_495_, sizeof(void*)*3);
if (v_kind_499_ == 0)
{
lean_object* v_sig_500_; lean_object* v___x_501_; lean_object* v_env_502_; uint8_t v___x_503_; 
v_sig_500_ = lean_ctor_get(v_val_495_, 1);
lean_inc_ref(v_sig_500_);
lean_dec(v_val_495_);
v___x_501_ = lean_st_ref_get(v_a_485_);
v_env_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc_ref(v_env_502_);
lean_dec(v___x_501_);
v___x_503_ = lean_is_matcher(v_env_502_, v_declName_481_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v_type_505_; lean_object* v___x_506_; 
lean_del_object(v___x_497_);
v___x_504_ = lean_task_get_own(v_sig_500_);
v_type_505_ = lean_ctor_get(v___x_504_, 2);
lean_inc_ref(v_type_505_);
lean_dec(v___x_504_);
v___x_506_ = l_Lean_Meta_isProp(v_type_505_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_521_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_521_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_521_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_521_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = lean_unbox(v_a_507_);
lean_dec(v_a_507_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = 1;
v___x_513_ = lean_box(v___x_512_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_513_);
v___x_515_ = v___x_509_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_box(v___x_503_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_517_);
v___x_519_ = v___x_509_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
return v___x_506_;
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec_ref(v_sig_500_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
v___x_522_ = lean_box(v___x_493_);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 0);
lean_ctor_set(v___x_497_, 0, v___x_522_);
v___x_524_ = v___x_497_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_del_object(v___x_497_);
lean_dec(v_val_495_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_declName_481_);
goto v___jp_487_;
}
}
}
else
{
lean_dec(v___x_494_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_declName_481_);
goto v___jp_487_;
}
v___jp_487_:
{
uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = 0;
v___x_489_ = lean_box(v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
return v_res_533_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_542_);
return v_res_544_;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_545_; lean_object* v___f_546_; 
v___x_545_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_546_ = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_546_, 0, v___x_545_);
return v___f_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___f_548_ = lean_obj_once(&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_box(1);
v___x_551_ = l_Lean_registerEnvExtension___redArg(v___f_548_, v___x_549_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; lean_object* v_env_558_; lean_object* v_toConstantVal_559_; lean_object* v_value_560_; lean_object* v_all_561_; uint8_t v___y_563_; lean_object* v_type_571_; uint8_t v___x_572_; 
v___x_557_ = lean_st_ref_get(v___y_555_);
v_env_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc_ref(v_env_558_);
lean_dec(v___x_557_);
v_toConstantVal_559_ = lean_ctor_get(v_thm_554_, 0);
v_value_560_ = lean_ctor_get(v_thm_554_, 1);
v_all_561_ = lean_ctor_get(v_thm_554_, 2);
v_type_571_ = lean_ctor_get(v_toConstantVal_559_, 2);
lean_inc_ref(v_env_558_);
v___x_572_ = l_Lean_Environment_hasUnsafe(v_env_558_, v_type_571_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; 
v___x_573_ = l_Lean_Environment_hasUnsafe(v_env_558_, v_value_560_);
v___y_563_ = v___x_573_;
goto v___jp_562_;
}
else
{
lean_dec_ref(v_env_558_);
v___y_563_ = v___x_572_;
goto v___jp_562_;
}
v___jp_562_:
{
if (v___y_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_564_, 0, v_thm_554_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_inc(v_all_561_);
lean_inc_ref(v_value_560_);
lean_inc_ref(v_toConstantVal_559_);
lean_dec_ref(v_thm_554_);
v___x_566_ = lean_box(0);
v___x_567_ = 0;
v___x_568_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_568_, 0, v_toConstantVal_559_);
lean_ctor_set(v___x_568_, 1, v_value_560_);
lean_ctor_set(v___x_568_, 2, v___x_566_);
lean_ctor_set(v___x_568_, 3, v_all_561_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*4, v___x_567_);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_574_, v___y_575_);
lean_dec(v___y_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_578_, v___y_582_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_592_, lean_object* v_b_593_, lean_object* v_c_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_apply_7(v_k_592_, v_b_593_, v_c_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, lean_box(0));
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_601_, lean_object* v_b_602_, lean_object* v_c_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_601_, v_b_602_, v_c_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_610_, lean_object* v_k_611_, uint8_t v_cleanupAnnotations_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___f_618_; uint8_t v___x_619_; uint8_t v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___f_618_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_618_, 0, v_k_611_);
v___x_619_ = 1;
v___x_620_ = 0;
v___x_621_ = lean_box(0);
v___x_622_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_610_, v___x_619_, v___x_620_, v___x_619_, v___x_620_, v___x_621_, v___f_618_, v_cleanupAnnotations_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
v_a_631_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_622_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_622_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_639_, lean_object* v_k_640_, lean_object* v_cleanupAnnotations_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_647_; lean_object* v_res_648_; 
v_cleanupAnnotations_boxed_647_ = lean_unbox(v_cleanupAnnotations_641_);
v_res_648_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_639_, v_k_640_, v_cleanupAnnotations_boxed_647_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_649_, lean_object* v_e_650_, lean_object* v_k_651_, uint8_t v_cleanupAnnotations_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_650_, v_k_651_, v_cleanupAnnotations_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_659_, lean_object* v_e_660_, lean_object* v_k_661_, lean_object* v_cleanupAnnotations_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_668_; lean_object* v_res_669_; 
v_cleanupAnnotations_boxed_668_ = lean_unbox(v_cleanupAnnotations_662_);
v_res_669_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_659_, v_e_660_, v_k_661_, v_cleanupAnnotations_boxed_668_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
if (lean_obj_tag(v_a_670_) == 0)
{
lean_object* v___x_672_; 
v___x_672_ = l_List_reverse___redArg(v_a_671_);
return v___x_672_;
}
else
{
lean_object* v_head_673_; lean_object* v_tail_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_683_; 
v_head_673_ = lean_ctor_get(v_a_670_, 0);
v_tail_674_ = lean_ctor_get(v_a_670_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_a_670_);
if (v_isSharedCheck_683_ == 0)
{
v___x_676_ = v_a_670_;
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_tail_674_);
lean_inc(v_head_673_);
lean_dec(v_a_670_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_mkLevelParam(v_head_673_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v_a_671_);
lean_ctor_set(v___x_676_, 0, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_a_671_);
v___x_680_ = v_reuseFailAlloc_682_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
v_a_670_ = v_tail_674_;
v_a_671_ = v___x_680_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_684_, lean_object* v_name_685_, lean_object* v_xs_686_, lean_object* v_body_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_name_693_; lean_object* v_levelParams_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_764_; 
v_name_693_ = lean_ctor_get(v_toConstantVal_684_, 0);
v_levelParams_694_ = lean_ctor_get(v_toConstantVal_684_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_toConstantVal_684_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v_toConstantVal_684_, 2);
lean_dec(v_unused_765_);
v___x_696_ = v_toConstantVal_684_;
v_isShared_697_ = v_isSharedCheck_764_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_levelParams_694_);
lean_inc(v_name_693_);
lean_dec(v_toConstantVal_684_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_764_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_lhs_701_; lean_object* v___x_702_; 
v___x_698_ = lean_box(0);
lean_inc(v_levelParams_694_);
v___x_699_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_694_, v___x_698_);
v___x_700_ = l_Lean_mkConst(v_name_693_, v___x_699_);
v_lhs_701_ = l_Lean_mkAppN(v___x_700_, v_xs_686_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc_ref(v_lhs_701_);
v___x_702_ = l_Lean_Meta_mkEq(v_lhs_701_, v_body_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; uint8_t v___x_704_; uint8_t v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
v___x_704_ = 0;
v___x_705_ = 1;
v___x_706_ = 1;
v___x_707_ = l_Lean_Meta_mkForallFVars(v_xs_686_, v_a_703_, v___x_704_, v___x_705_, v___x_705_, v___x_706_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
v___x_709_ = l_Lean_Meta_letToHave(v_a_708_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_709_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
v___x_711_ = l_Lean_Meta_mkEqRefl(v_lhs_701_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___x_713_ = l_Lean_Meta_mkLambdaFVars(v_xs_686_, v_a_712_, v___x_704_, v___x_705_, v___x_704_, v___x_705_, v___x_706_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref(v___x_713_);
lean_inc(v_name_685_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 2, v_a_710_);
lean_ctor_set(v___x_696_, 0, v_name_685_);
v___x_716_ = v___x_696_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_name_685_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_levelParams_694_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_a_710_);
v___x_716_ = v_reuseFailAlloc_723_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_721_; 
lean_inc(v_name_685_);
v___x_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_717_, 0, v_name_685_);
lean_ctor_set(v___x_717_, 1, v___x_698_);
v___x_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v_a_714_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
v___x_719_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_718_, v___y_691_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_719_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
v___x_721_ = l_Lean_addDecl(v_a_720_, v___x_704_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; 
lean_dec_ref(v___x_721_);
v___x_722_ = l_Lean_inferDefEqAttr(v_name_685_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v___x_722_;
}
else
{
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_name_685_);
return v___x_721_;
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_710_);
lean_del_object(v___x_696_);
lean_dec(v_levelParams_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_name_685_);
v_a_724_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_713_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_713_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_710_);
lean_del_object(v___x_696_);
lean_dec(v_levelParams_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_name_685_);
v_a_732_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_711_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_711_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v_lhs_701_);
lean_del_object(v___x_696_);
lean_dec(v_levelParams_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_name_685_);
v_a_740_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_709_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_709_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v_lhs_701_);
lean_del_object(v___x_696_);
lean_dec(v_levelParams_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_name_685_);
v_a_748_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_707_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_707_);
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
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_lhs_701_);
lean_del_object(v___x_696_);
lean_dec(v_levelParams_694_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_name_685_);
v_a_756_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_702_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_702_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_766_, lean_object* v_name_767_, lean_object* v_xs_768_, lean_object* v_body_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_766_, v_name_767_, v_xs_768_, v_body_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec_ref(v_xs_768_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_776_, lean_object* v_info_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_toConstantVal_783_; lean_object* v_value_784_; lean_object* v___f_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v_toConstantVal_783_ = lean_ctor_get(v_info_777_, 0);
lean_inc_ref(v_toConstantVal_783_);
v_value_784_ = lean_ctor_get(v_info_777_, 1);
lean_inc_ref(v_value_784_);
lean_dec_ref(v_info_777_);
v___f_785_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_785_, 0, v_toConstantVal_783_);
lean_closure_set(v___f_785_, 1, v_name_776_);
v___x_786_ = 1;
v___x_787_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_784_, v___f_785_, v___x_786_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_788_, lean_object* v_info_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_788_, v_info_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_796_, lean_object* v_name_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_806_; lean_object* v_env_807_; uint8_t v___x_808_; lean_object* v___x_809_; 
v___x_806_ = lean_st_ref_get(v_a_801_);
v_env_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_ref(v_env_807_);
lean_dec(v___x_806_);
v___x_808_ = 0;
lean_inc(v_declName_796_);
v___x_809_ = l_Lean_Environment_find_x3f(v_env_807_, v_declName_796_, v___x_808_);
if (lean_obj_tag(v___x_809_) == 1)
{
lean_object* v_val_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_836_; 
v_val_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_836_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_836_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_val_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_836_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
if (lean_obj_tag(v_val_810_) == 1)
{
lean_object* v_val_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_val_814_ = lean_ctor_get(v_val_810_, 0);
lean_inc_ref(v_val_814_);
lean_dec_ref(v_val_810_);
lean_inc(v_name_797_);
v___x_815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_815_, 0, v_name_797_);
lean_closure_set(v___x_815_, 1, v_val_814_);
lean_inc(v_name_797_);
v___x_816_ = l_Lean_Meta_realizeConst(v_declName_796_, v_name_797_, v___x_815_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_826_; 
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v___x_816_, 0);
lean_dec(v_unused_827_);
v___x_818_ = v___x_816_;
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
else
{
lean_dec(v___x_816_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v_name_797_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_name_797_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_823_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_821_);
v___x_823_ = v___x_818_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_del_object(v___x_812_);
lean_dec(v_name_797_);
v_a_828_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_816_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_816_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_del_object(v___x_812_);
lean_dec(v_val_810_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_name_797_);
lean_dec(v_declName_796_);
goto v___jp_803_;
}
}
}
else
{
lean_dec(v___x_809_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_name_797_);
lean_dec(v_declName_796_);
goto v___jp_803_;
}
v___jp_803_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_837_, lean_object* v_name_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_mkSimpleEqThm(v_declName_837_, v_name_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_845_, lean_object* v_vals_846_, lean_object* v_i_847_, lean_object* v_k_848_){
_start:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_array_get_size(v_keys_845_);
v___x_850_ = lean_nat_dec_lt(v_i_847_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec(v_i_847_);
v___x_851_ = lean_box(0);
return v___x_851_;
}
else
{
lean_object* v_k_x27_852_; uint8_t v___x_853_; 
v_k_x27_852_ = lean_array_fget_borrowed(v_keys_845_, v_i_847_);
v___x_853_ = lean_name_eq(v_k_848_, v_k_x27_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_nat_add(v_i_847_, v___x_854_);
lean_dec(v_i_847_);
v_i_847_ = v___x_855_;
goto _start;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_array_fget_borrowed(v_vals_846_, v_i_847_);
lean_dec(v_i_847_);
lean_inc(v___x_857_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_859_, lean_object* v_vals_860_, lean_object* v_i_861_, lean_object* v_k_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_859_, v_vals_860_, v_i_861_, v_k_862_);
lean_dec(v_k_862_);
lean_dec_ref(v_vals_860_);
lean_dec_ref(v_keys_859_);
return v_res_863_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; 
v___x_864_ = ((size_t)5ULL);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_shift_left(v___x_865_, v___x_864_);
return v___x_866_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_867_; size_t v___x_868_; size_t v___x_869_; 
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_869_ = lean_usize_sub(v___x_868_, v___x_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_870_, size_t v_x_871_, lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_870_) == 0)
{
lean_object* v_es_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_894_; 
v_es_873_ = lean_ctor_get(v_x_870_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_870_);
if (v_isSharedCheck_894_ == 0)
{
v___x_875_ = v_x_870_;
v_isShared_876_ = v_isSharedCheck_894_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_es_873_);
lean_dec(v_x_870_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_894_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; lean_object* v_j_881_; lean_object* v___x_882_; 
v___x_877_ = lean_box(2);
v___x_878_ = ((size_t)5ULL);
v___x_879_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_880_ = lean_usize_land(v_x_871_, v___x_879_);
v_j_881_ = lean_usize_to_nat(v___x_880_);
v___x_882_ = lean_array_get(v___x_877_, v_es_873_, v_j_881_);
lean_dec(v_j_881_);
lean_dec_ref(v_es_873_);
switch(lean_obj_tag(v___x_882_))
{
case 0:
{
lean_object* v_key_883_; lean_object* v_val_884_; uint8_t v___x_885_; 
v_key_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_key_883_);
v_val_884_ = lean_ctor_get(v___x_882_, 1);
lean_inc(v_val_884_);
lean_dec_ref(v___x_882_);
v___x_885_ = lean_name_eq(v_x_872_, v_key_883_);
lean_dec(v_key_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v_val_884_);
lean_del_object(v___x_875_);
v___x_886_ = lean_box(0);
return v___x_886_;
}
else
{
lean_object* v___x_888_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
lean_ctor_set(v___x_875_, 0, v_val_884_);
v___x_888_ = v___x_875_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_val_884_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
case 1:
{
lean_object* v_node_890_; size_t v___x_891_; 
lean_del_object(v___x_875_);
v_node_890_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_node_890_);
lean_dec_ref(v___x_882_);
v___x_891_ = lean_usize_shift_right(v_x_871_, v___x_878_);
v_x_870_ = v_node_890_;
v_x_871_ = v___x_891_;
goto _start;
}
default: 
{
lean_object* v___x_893_; 
lean_del_object(v___x_875_);
v___x_893_ = lean_box(0);
return v___x_893_;
}
}
}
}
else
{
lean_object* v_ks_895_; lean_object* v_vs_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_ks_895_ = lean_ctor_get(v_x_870_, 0);
lean_inc_ref(v_ks_895_);
v_vs_896_ = lean_ctor_get(v_x_870_, 1);
lean_inc_ref(v_vs_896_);
lean_dec_ref(v_x_870_);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_895_, v_vs_896_, v___x_897_, v_x_872_);
lean_dec_ref(v_vs_896_);
lean_dec_ref(v_ks_895_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
size_t v_x_468__boxed_902_; lean_object* v_res_903_; 
v_x_468__boxed_902_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_903_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_899_, v_x_468__boxed_902_, v_x_901_);
lean_dec(v_x_901_);
return v_res_903_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_904_; uint64_t v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(1723u);
v___x_905_ = lean_uint64_of_nat(v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
uint64_t v___y_909_; 
if (lean_obj_tag(v_x_907_) == 0)
{
uint64_t v___x_912_; 
v___x_912_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_909_ = v___x_912_;
goto v___jp_908_;
}
else
{
uint64_t v_hash_913_; 
v_hash_913_ = lean_ctor_get_uint64(v_x_907_, sizeof(void*)*2);
v___y_909_ = v_hash_913_;
goto v___jp_908_;
}
v___jp_908_:
{
size_t v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_uint64_to_usize(v___y_909_);
v___x_911_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_906_, v___x_910_, v_x_907_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_914_, v_x_915_);
lean_dec(v_x_915_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_env_921_; lean_object* v___x_922_; lean_object* v_asyncMode_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_920_ = lean_st_ref_get(v_a_918_);
v_env_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc_ref(v_env_921_);
lean_dec(v___x_920_);
v___x_922_ = l_Lean_Meta_eqnsExt;
v_asyncMode_923_ = lean_ctor_get(v___x_922_, 2);
lean_inc(v_asyncMode_923_);
v___x_924_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_925_ = lean_box(0);
v___x_926_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_924_, v___x_922_, v_env_921_, v_asyncMode_923_, v___x_925_);
lean_dec(v_asyncMode_923_);
v___x_927_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_926_, v_thmName_917_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec(v_thmName_929_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_933_, v_a_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_thmName_938_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_947_, v_x_948_, v_x_949_);
lean_dec(v_x_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, size_t v_x_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_952_, v_x_953_, v_x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
size_t v_x_594__boxed_960_; lean_object* v_res_961_; 
v_x_594__boxed_960_ = lean_unbox_usize(v_x_958_);
lean_dec(v_x_958_);
v_res_961_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_956_, v_x_957_, v_x_594__boxed_960_, v_x_959_);
lean_dec(v_x_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_962_, lean_object* v_keys_963_, lean_object* v_vals_964_, lean_object* v_heq_965_, lean_object* v_i_966_, lean_object* v_k_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_963_, v_vals_964_, v_i_966_, v_k_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_969_, lean_object* v_keys_970_, lean_object* v_vals_971_, lean_object* v_heq_972_, lean_object* v_i_973_, lean_object* v_k_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_969_, v_keys_970_, v_vals_971_, v_heq_972_, v_i_973_, v_k_974_);
lean_dec(v_k_974_);
lean_dec_ref(v_vals_971_);
lean_dec_ref(v_keys_970_);
return v_res_975_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_976_, lean_object* v_i_977_, lean_object* v_k_978_){
_start:
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_array_get_size(v_keys_976_);
v___x_980_ = lean_nat_dec_lt(v_i_977_, v___x_979_);
if (v___x_980_ == 0)
{
lean_dec(v_i_977_);
return v___x_980_;
}
else
{
lean_object* v_k_x27_981_; uint8_t v___x_982_; 
v_k_x27_981_ = lean_array_fget_borrowed(v_keys_976_, v_i_977_);
v___x_982_ = lean_name_eq(v_k_978_, v_k_x27_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_add(v_i_977_, v___x_983_);
lean_dec(v_i_977_);
v_i_977_ = v___x_984_;
goto _start;
}
else
{
lean_dec(v_i_977_);
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_986_, lean_object* v_i_987_, lean_object* v_k_988_){
_start:
{
uint8_t v_res_989_; lean_object* v_r_990_; 
v_res_989_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_986_, v_i_987_, v_k_988_);
lean_dec(v_k_988_);
lean_dec_ref(v_keys_986_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_991_, size_t v_x_992_, lean_object* v_x_993_){
_start:
{
if (lean_obj_tag(v_x_991_) == 0)
{
lean_object* v_es_994_; lean_object* v___x_995_; size_t v___x_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v_j_999_; lean_object* v___x_1000_; 
v_es_994_ = lean_ctor_get(v_x_991_, 0);
lean_inc_ref(v_es_994_);
lean_dec_ref(v_x_991_);
v___x_995_ = lean_box(2);
v___x_996_ = ((size_t)5ULL);
v___x_997_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_998_ = lean_usize_land(v_x_992_, v___x_997_);
v_j_999_ = lean_usize_to_nat(v___x_998_);
v___x_1000_ = lean_array_get(v___x_995_, v_es_994_, v_j_999_);
lean_dec(v_j_999_);
lean_dec_ref(v_es_994_);
switch(lean_obj_tag(v___x_1000_))
{
case 0:
{
lean_object* v_key_1001_; uint8_t v___x_1002_; 
v_key_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_key_1001_);
lean_dec_ref(v___x_1000_);
v___x_1002_ = lean_name_eq(v_x_993_, v_key_1001_);
lean_dec(v_key_1001_);
return v___x_1002_;
}
case 1:
{
lean_object* v_node_1003_; size_t v___x_1004_; 
v_node_1003_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_node_1003_);
lean_dec_ref(v___x_1000_);
v___x_1004_ = lean_usize_shift_right(v_x_992_, v___x_996_);
v_x_991_ = v_node_1003_;
v_x_992_ = v___x_1004_;
goto _start;
}
default: 
{
uint8_t v___x_1006_; 
v___x_1006_ = 0;
return v___x_1006_;
}
}
}
else
{
lean_object* v_ks_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_ks_1007_ = lean_ctor_get(v_x_991_, 0);
lean_inc_ref(v_ks_1007_);
lean_dec_ref(v_x_991_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1007_, v___x_1008_, v_x_993_);
lean_dec_ref(v_ks_1007_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
size_t v_x_448__boxed_1013_; uint8_t v_res_1014_; lean_object* v_r_1015_; 
v_x_448__boxed_1013_ = lean_unbox_usize(v_x_1011_);
lean_dec(v_x_1011_);
v_res_1014_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1010_, v_x_448__boxed_1013_, v_x_1012_);
lean_dec(v_x_1012_);
v_r_1015_ = lean_box(v_res_1014_);
return v_r_1015_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
uint64_t v___y_1019_; 
if (lean_obj_tag(v_x_1017_) == 0)
{
uint64_t v___x_1022_; 
v___x_1022_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1019_ = v___x_1022_;
goto v___jp_1018_;
}
else
{
uint64_t v_hash_1023_; 
v_hash_1023_ = lean_ctor_get_uint64(v_x_1017_, sizeof(void*)*2);
v___y_1019_ = v_hash_1023_;
goto v___jp_1018_;
}
v___jp_1018_:
{
size_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_uint64_to_usize(v___y_1019_);
v___x_1021_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1016_, v___x_1020_, v_x_1017_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1024_, v_x_1025_);
lean_dec(v_x_1025_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v_env_1032_; lean_object* v___x_1033_; lean_object* v_asyncMode_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1031_ = lean_st_ref_get(v_a_1029_);
v_env_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc_ref(v_env_1032_);
lean_dec(v___x_1031_);
v___x_1033_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1034_ = lean_ctor_get(v___x_1033_, 2);
lean_inc(v_asyncMode_1034_);
v___x_1035_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1036_ = lean_box(0);
v___x_1037_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1035_, v___x_1033_, v_env_1032_, v_asyncMode_1034_, v___x_1036_);
lean_dec(v_asyncMode_1034_);
v___x_1038_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1037_, v_thmName_1028_);
v___x_1039_ = lean_box(v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec(v_thmName_1041_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1045_, v_a_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Meta_isEqnThm(v_thmName_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_thmName_1050_);
return v_res_1054_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1056_, v_x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1059_, v_x_1060_, v_x_1061_);
lean_dec(v_x_1061_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1064_, lean_object* v_x_1065_, size_t v_x_1066_, lean_object* v_x_1067_){
_start:
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1065_, v_x_1066_, v_x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
size_t v_x_551__boxed_1073_; uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_x_551__boxed_1073_ = lean_unbox_usize(v_x_1071_);
lean_dec(v_x_1071_);
v_res_1074_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1069_, v_x_1070_, v_x_551__boxed_1073_, v_x_1072_);
lean_dec(v_x_1072_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1076_, lean_object* v_keys_1077_, lean_object* v_vals_1078_, lean_object* v_heq_1079_, lean_object* v_i_1080_, lean_object* v_k_1081_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1077_, v_i_1080_, v_k_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1083_, lean_object* v_keys_1084_, lean_object* v_vals_1085_, lean_object* v_heq_1086_, lean_object* v_i_1087_, lean_object* v_k_1088_){
_start:
{
uint8_t v_res_1089_; lean_object* v_r_1090_; 
v_res_1089_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1083_, v_keys_1084_, v_vals_1085_, v_heq_1086_, v_i_1087_, v_k_1088_);
lean_dec(v_k_1088_);
lean_dec_ref(v_vals_1085_);
lean_dec_ref(v_keys_1084_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v_ks_1095_; lean_object* v_vs_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1120_; 
v_ks_1095_ = lean_ctor_get(v_x_1091_, 0);
v_vs_1096_ = lean_ctor_get(v_x_1091_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1098_ = v_x_1091_;
v_isShared_1099_ = v_isSharedCheck_1120_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_vs_1096_);
lean_inc(v_ks_1095_);
lean_dec(v_x_1091_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1120_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_array_get_size(v_ks_1095_);
v___x_1101_ = lean_nat_dec_lt(v_x_1092_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_dec(v_x_1092_);
v___x_1102_ = lean_array_push(v_ks_1095_, v_x_1093_);
v___x_1103_ = lean_array_push(v_vs_1096_, v_x_1094_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1103_);
lean_ctor_set(v___x_1098_, 0, v___x_1102_);
v___x_1105_ = v___x_1098_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
lean_object* v_k_x27_1107_; uint8_t v___x_1108_; 
v_k_x27_1107_ = lean_array_fget_borrowed(v_ks_1095_, v_x_1092_);
v___x_1108_ = lean_name_eq(v_x_1093_, v_k_x27_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1110_; 
if (v_isShared_1099_ == 0)
{
v___x_1110_ = v___x_1098_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_ks_1095_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_vs_1096_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_x_1092_, v___x_1111_);
lean_dec(v_x_1092_);
v_x_1091_ = v___x_1110_;
v_x_1092_ = v___x_1112_;
goto _start;
}
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1115_ = lean_array_fset(v_ks_1095_, v_x_1092_, v_x_1093_);
v___x_1116_ = lean_array_fset(v_vs_1096_, v_x_1092_, v_x_1094_);
lean_dec(v_x_1092_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1116_);
lean_ctor_set(v___x_1098_, 0, v___x_1115_);
v___x_1118_ = v___x_1098_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1121_, lean_object* v_k_1122_, lean_object* v_v_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1121_, v___x_1124_, v_k_1122_, v_v_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1127_, size_t v_x_1128_, size_t v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
lean_object* v_es_1132_; size_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; lean_object* v_j_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_es_1132_ = lean_ctor_get(v_x_1127_, 0);
v___x_1133_ = ((size_t)5ULL);
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1136_ = lean_usize_land(v_x_1128_, v___x_1135_);
v_j_1137_ = lean_usize_to_nat(v___x_1136_);
v___x_1138_ = lean_array_get_size(v_es_1132_);
v___x_1139_ = lean_nat_dec_lt(v_j_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_dec(v_j_1137_);
lean_dec(v_x_1131_);
lean_dec(v_x_1130_);
return v_x_1127_;
}
else
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1176_; 
lean_inc_ref(v_es_1132_);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v_x_1127_, 0);
lean_dec(v_unused_1177_);
v___x_1141_ = v_x_1127_;
v_isShared_1142_ = v_isSharedCheck_1176_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_x_1127_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1176_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_v_1143_; lean_object* v___x_1144_; lean_object* v_xs_x27_1145_; lean_object* v___y_1147_; 
v_v_1143_ = lean_array_fget(v_es_1132_, v_j_1137_);
v___x_1144_ = lean_box(0);
v_xs_x27_1145_ = lean_array_fset(v_es_1132_, v_j_1137_, v___x_1144_);
switch(lean_obj_tag(v_v_1143_))
{
case 0:
{
lean_object* v_key_1152_; lean_object* v_val_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1163_; 
v_key_1152_ = lean_ctor_get(v_v_1143_, 0);
v_val_1153_ = lean_ctor_get(v_v_1143_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_v_1143_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1155_ = v_v_1143_;
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_val_1153_);
lean_inc(v_key_1152_);
lean_dec(v_v_1143_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_name_eq(v_x_1130_, v_key_1152_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_del_object(v___x_1155_);
v___x_1158_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1152_, v_val_1153_, v_x_1130_, v_x_1131_);
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
v___y_1147_ = v___x_1159_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1161_; 
lean_dec(v_val_1153_);
lean_dec(v_key_1152_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v_x_1131_);
lean_ctor_set(v___x_1155_, 0, v_x_1130_);
v___x_1161_ = v___x_1155_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_x_1130_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_x_1131_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
v___y_1147_ = v___x_1161_;
goto v___jp_1146_;
}
}
}
}
case 1:
{
lean_object* v_node_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1174_; 
v_node_1164_ = lean_ctor_get(v_v_1143_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_v_1143_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1166_ = v_v_1143_;
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_node_1164_);
lean_dec(v_v_1143_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1168_ = lean_usize_shift_right(v_x_1128_, v___x_1133_);
v___x_1169_ = lean_usize_add(v_x_1129_, v___x_1134_);
v___x_1170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1164_, v___x_1168_, v___x_1169_, v_x_1130_, v_x_1131_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1170_);
v___x_1172_ = v___x_1166_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
v___y_1147_ = v___x_1172_;
goto v___jp_1146_;
}
}
}
default: 
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_x_1130_);
lean_ctor_set(v___x_1175_, 1, v_x_1131_);
v___y_1147_ = v___x_1175_;
goto v___jp_1146_;
}
}
v___jp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_array_fset(v_xs_x27_1145_, v_j_1137_, v___y_1147_);
lean_dec(v_j_1137_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1148_);
v___x_1150_ = v___x_1141_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
lean_object* v_ks_1178_; lean_object* v_vs_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1199_; 
v_ks_1178_ = lean_ctor_get(v_x_1127_, 0);
v_vs_1179_ = lean_ctor_get(v_x_1127_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1181_ = v_x_1127_;
v_isShared_1182_ = v_isSharedCheck_1199_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_vs_1179_);
lean_inc(v_ks_1178_);
lean_dec(v_x_1127_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1199_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_ks_1178_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_vs_1179_);
v___x_1184_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v_newNode_1185_; uint8_t v___y_1187_; size_t v___x_1193_; uint8_t v___x_1194_; 
v_newNode_1185_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1184_, v_x_1130_, v_x_1131_);
v___x_1193_ = ((size_t)7ULL);
v___x_1194_ = lean_usize_dec_le(v___x_1193_, v_x_1129_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1185_);
v___x_1196_ = lean_unsigned_to_nat(4u);
v___x_1197_ = lean_nat_dec_lt(v___x_1195_, v___x_1196_);
lean_dec(v___x_1195_);
v___y_1187_ = v___x_1197_;
goto v___jp_1186_;
}
else
{
v___y_1187_ = v___x_1194_;
goto v___jp_1186_;
}
v___jp_1186_:
{
if (v___y_1187_ == 0)
{
lean_object* v_ks_1188_; lean_object* v_vs_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_ks_1188_ = lean_ctor_get(v_newNode_1185_, 0);
lean_inc_ref(v_ks_1188_);
v_vs_1189_ = lean_ctor_get(v_newNode_1185_, 1);
lean_inc_ref(v_vs_1189_);
lean_dec_ref(v_newNode_1185_);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1129_, v_ks_1188_, v_vs_1189_, v___x_1190_, v___x_1191_);
lean_dec_ref(v_vs_1189_);
lean_dec_ref(v_ks_1188_);
return v___x_1192_;
}
else
{
return v_newNode_1185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1200_, lean_object* v_keys_1201_, lean_object* v_vals_1202_, lean_object* v_i_1203_, lean_object* v_entries_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_array_get_size(v_keys_1201_);
v___x_1206_ = lean_nat_dec_lt(v_i_1203_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_dec(v_i_1203_);
return v_entries_1204_;
}
else
{
lean_object* v_k_1207_; lean_object* v_v_1208_; uint64_t v___y_1210_; 
v_k_1207_ = lean_array_fget_borrowed(v_keys_1201_, v_i_1203_);
v_v_1208_ = lean_array_fget_borrowed(v_vals_1202_, v_i_1203_);
if (lean_obj_tag(v_k_1207_) == 0)
{
uint64_t v___x_1221_; 
v___x_1221_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1210_ = v___x_1221_;
goto v___jp_1209_;
}
else
{
uint64_t v_hash_1222_; 
v_hash_1222_ = lean_ctor_get_uint64(v_k_1207_, sizeof(void*)*2);
v___y_1210_ = v_hash_1222_;
goto v___jp_1209_;
}
v___jp_1209_:
{
size_t v_h_1211_; size_t v___x_1212_; lean_object* v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; size_t v_h_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_h_1211_ = lean_uint64_to_usize(v___y_1210_);
v___x_1212_ = ((size_t)5ULL);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_sub(v_depth_1200_, v___x_1214_);
v___x_1216_ = lean_usize_mul(v___x_1212_, v___x_1215_);
v_h_1217_ = lean_usize_shift_right(v_h_1211_, v___x_1216_);
v___x_1218_ = lean_nat_add(v_i_1203_, v___x_1213_);
lean_dec(v_i_1203_);
lean_inc(v_v_1208_);
lean_inc(v_k_1207_);
v___x_1219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1204_, v_h_1217_, v_depth_1200_, v_k_1207_, v_v_1208_);
v_i_1203_ = v___x_1218_;
v_entries_1204_ = v___x_1219_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1223_, lean_object* v_keys_1224_, lean_object* v_vals_1225_, lean_object* v_i_1226_, lean_object* v_entries_1227_){
_start:
{
size_t v_depth_boxed_1228_; lean_object* v_res_1229_; 
v_depth_boxed_1228_ = lean_unbox_usize(v_depth_1223_);
lean_dec(v_depth_1223_);
v_res_1229_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1228_, v_keys_1224_, v_vals_1225_, v_i_1226_, v_entries_1227_);
lean_dec_ref(v_vals_1225_);
lean_dec_ref(v_keys_1224_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
size_t v_x_638__boxed_1235_; size_t v_x_639__boxed_1236_; lean_object* v_res_1237_; 
v_x_638__boxed_1235_ = lean_unbox_usize(v_x_1231_);
lean_dec(v_x_1231_);
v_x_639__boxed_1236_ = lean_unbox_usize(v_x_1232_);
lean_dec(v_x_1232_);
v_res_1237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1230_, v_x_638__boxed_1235_, v_x_639__boxed_1236_, v_x_1233_, v_x_1234_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_){
_start:
{
uint64_t v___y_1242_; 
if (lean_obj_tag(v_x_1239_) == 0)
{
uint64_t v___x_1246_; 
v___x_1246_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1242_ = v___x_1246_;
goto v___jp_1241_;
}
else
{
uint64_t v_hash_1247_; 
v_hash_1247_ = lean_ctor_get_uint64(v_x_1239_, sizeof(void*)*2);
v___y_1242_ = v_hash_1247_;
goto v___jp_1241_;
}
v___jp_1241_:
{
size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_uint64_to_usize(v___y_1242_);
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1238_, v___x_1243_, v___x_1244_, v_x_1239_, v_x_1240_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1248_, lean_object* v_as_1249_, size_t v_i_1250_, size_t v_stop_1251_, lean_object* v_b_1252_){
_start:
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_eq(v_i_1250_, v_stop_1251_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; 
v___x_1254_ = lean_array_uget_borrowed(v_as_1249_, v_i_1250_);
lean_inc(v_declName_1248_);
lean_inc(v___x_1254_);
v___x_1255_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1252_, v___x_1254_, v_declName_1248_);
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_add(v_i_1250_, v___x_1256_);
v_i_1250_ = v___x_1257_;
v_b_1252_ = v___x_1255_;
goto _start;
}
else
{
lean_dec(v_declName_1248_);
return v_b_1252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1259_, lean_object* v_as_1260_, lean_object* v_i_1261_, lean_object* v_stop_1262_, lean_object* v_b_1263_){
_start:
{
size_t v_i_boxed_1264_; size_t v_stop_boxed_1265_; lean_object* v_res_1266_; 
v_i_boxed_1264_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_stop_boxed_1265_ = lean_unbox_usize(v_stop_1262_);
lean_dec(v_stop_1262_);
v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1259_, v_as_1260_, v_i_boxed_1264_, v_stop_boxed_1265_, v_b_1263_);
lean_dec_ref(v_as_1260_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1267_, lean_object* v_declName_1268_, lean_object* v_s_1269_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_array_get_size(v_eqThms_1267_);
v___x_1272_ = lean_nat_dec_lt(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v_declName_1268_);
return v_s_1269_;
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_nat_dec_le(v___x_1271_, v___x_1271_);
if (v___x_1273_ == 0)
{
if (v___x_1272_ == 0)
{
lean_dec(v_declName_1268_);
return v_s_1269_;
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_of_nat(v___x_1271_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1268_, v_eqThms_1267_, v___x_1274_, v___x_1275_, v_s_1269_);
return v___x_1276_;
}
}
else
{
size_t v___x_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = ((size_t)0ULL);
v___x_1278_ = lean_usize_of_nat(v___x_1271_);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1268_, v_eqThms_1267_, v___x_1277_, v___x_1278_, v_s_1269_);
return v___x_1279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1280_, lean_object* v_declName_1281_, lean_object* v_s_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1280_, v_declName_1281_, v_s_1282_);
lean_dec_ref(v_eqThms_1280_);
return v_res_1283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0(void){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1289_, lean_object* v_eqThms_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v_env_1294_; lean_object* v_nextMacroScope_1295_; lean_object* v_ngen_1296_; lean_object* v_auxDeclNGen_1297_; lean_object* v_traceState_1298_; lean_object* v_messages_1299_; lean_object* v_infoState_1300_; lean_object* v_snapshotTasks_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1317_; 
v___x_1293_ = lean_st_ref_take(v_a_1291_);
v_env_1294_ = lean_ctor_get(v___x_1293_, 0);
v_nextMacroScope_1295_ = lean_ctor_get(v___x_1293_, 1);
v_ngen_1296_ = lean_ctor_get(v___x_1293_, 2);
v_auxDeclNGen_1297_ = lean_ctor_get(v___x_1293_, 3);
v_traceState_1298_ = lean_ctor_get(v___x_1293_, 4);
v_messages_1299_ = lean_ctor_get(v___x_1293_, 6);
v_infoState_1300_ = lean_ctor_get(v___x_1293_, 7);
v_snapshotTasks_1301_ = lean_ctor_get(v___x_1293_, 8);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1293_, 5);
lean_dec(v_unused_1318_);
v___x_1303_ = v___x_1293_;
v_isShared_1304_ = v_isSharedCheck_1317_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_snapshotTasks_1301_);
lean_inc(v_infoState_1300_);
lean_inc(v_messages_1299_);
lean_inc(v_traceState_1298_);
lean_inc(v_auxDeclNGen_1297_);
lean_inc(v_ngen_1296_);
lean_inc(v_nextMacroScope_1295_);
lean_inc(v_env_1294_);
lean_dec(v___x_1293_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1317_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v_asyncMode_1306_; lean_object* v___f_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1305_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1306_ = lean_ctor_get(v___x_1305_, 2);
lean_inc(v_asyncMode_1306_);
v___f_1307_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1307_, 0, v_eqThms_1290_);
lean_closure_set(v___f_1307_, 1, v_declName_1289_);
v___x_1308_ = lean_box(0);
v___x_1309_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1305_, v_env_1294_, v___f_1307_, v_asyncMode_1306_, v___x_1308_);
lean_dec(v_asyncMode_1306_);
v___x_1310_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 5, v___x_1310_);
lean_ctor_set(v___x_1303_, 0, v___x_1309_);
v___x_1312_ = v___x_1303_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_nextMacroScope_1295_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_ngen_1296_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_auxDeclNGen_1297_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_traceState_1298_);
lean_ctor_set(v_reuseFailAlloc_1316_, 5, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1316_, 6, v_messages_1299_);
lean_ctor_set(v_reuseFailAlloc_1316_, 7, v_infoState_1300_);
lean_ctor_set(v_reuseFailAlloc_1316_, 8, v_snapshotTasks_1301_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_st_ref_set(v_a_1291_, v___x_1312_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1319_, lean_object* v_eqThms_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1319_, v_eqThms_1320_, v_a_1321_);
lean_dec(v_a_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1324_, lean_object* v_eqThms_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1324_, v_eqThms_1325_, v_a_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1330_, lean_object* v_eqThms_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1330_, v_eqThms_1331_, v_a_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1337_, v_x_1338_, v_x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1341_, lean_object* v_x_1342_, size_t v_x_1343_, size_t v_x_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1342_, v_x_1343_, v_x_1344_, v_x_1345_, v_x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
size_t v_x_925__boxed_1354_; size_t v_x_926__boxed_1355_; lean_object* v_res_1356_; 
v_x_925__boxed_1354_ = lean_unbox_usize(v_x_1350_);
lean_dec(v_x_1350_);
v_x_926__boxed_1355_ = lean_unbox_usize(v_x_1351_);
lean_dec(v_x_1351_);
v_res_1356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1348_, v_x_1349_, v_x_925__boxed_1354_, v_x_926__boxed_1355_, v_x_1352_, v_x_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1357_, lean_object* v_n_1358_, lean_object* v_k_1359_, lean_object* v_v_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1358_, v_k_1359_, v_v_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1362_, size_t v_depth_1363_, lean_object* v_keys_1364_, lean_object* v_vals_1365_, lean_object* v_heq_1366_, lean_object* v_i_1367_, lean_object* v_entries_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1363_, v_keys_1364_, v_vals_1365_, v_i_1367_, v_entries_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1370_, lean_object* v_depth_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_heq_1374_, lean_object* v_i_1375_, lean_object* v_entries_1376_){
_start:
{
size_t v_depth_boxed_1377_; lean_object* v_res_1378_; 
v_depth_boxed_1377_ = lean_unbox_usize(v_depth_1371_);
lean_dec(v_depth_1371_);
v_res_1378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1370_, v_depth_boxed_1377_, v_keys_1372_, v_vals_1373_, v_heq_1374_, v_i_1375_, v_entries_1376_);
lean_dec_ref(v_vals_1373_);
lean_dec_ref(v_keys_1372_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1380_, v_x_1381_, v_x_1382_, v_x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1385_, lean_object* v_env_1386_, lean_object* v_idx_1387_, lean_object* v_eqs_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_nextEq_1395_; uint8_t v___x_1396_; 
v___x_1390_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v_idx_1387_, v___x_1391_);
lean_dec(v_idx_1387_);
lean_inc(v___x_1392_);
v___x_1393_ = l_Nat_reprFast(v___x_1392_);
v___x_1394_ = lean_string_append(v___x_1390_, v___x_1393_);
lean_dec_ref(v___x_1393_);
lean_inc(v_declName_1385_);
lean_inc_ref(v_env_1386_);
v_nextEq_1395_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1386_, v_declName_1385_, v___x_1394_);
lean_inc_ref(v_env_1386_);
v___x_1396_ = l_Lean_Environment_containsOnBranch(v_env_1386_, v_nextEq_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v_nextEq_1395_);
lean_dec(v___x_1392_);
lean_dec_ref(v_env_1386_);
lean_dec(v_declName_1385_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_eqs_1388_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_array_push(v_eqs_1388_, v_nextEq_1395_);
v_idx_1387_ = v___x_1392_;
v_eqs_1388_ = v___x_1398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1400_, lean_object* v_env_1401_, lean_object* v_idx_1402_, lean_object* v_eqs_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1400_, v_env_1401_, v_idx_1402_, v_eqs_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1406_, lean_object* v_env_1407_, lean_object* v_idx_1408_, lean_object* v_eqs_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1406_, v_env_1407_, v_idx_1408_, v_eqs_1409_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1416_, lean_object* v_env_1417_, lean_object* v_idx_1418_, lean_object* v_eqs_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1416_, v_env_1417_, v_idx_1418_, v_eqs_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1429_; lean_object* v_env_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1429_ = lean_st_ref_get(v_a_1427_);
v_env_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc_ref(v_env_1430_);
lean_dec(v___x_1429_);
v___x_1431_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1426_);
lean_inc_ref(v_env_1430_);
v___x_1432_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1430_, v_declName_1426_, v___x_1431_);
v___x_1433_ = 1;
lean_inc(v___x_1432_);
lean_inc_ref(v_env_1430_);
v___x_1434_ = l_Lean_Environment_contains(v_env_1430_, v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v___x_1432_);
lean_dec_ref(v_env_1430_);
lean_dec(v_declName_1426_);
v___x_1435_ = lean_box(0);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1438_ = lean_mk_empty_array_with_capacity(v___x_1437_);
v___x_1439_ = lean_array_push(v___x_1438_, v___x_1432_);
lean_inc(v_declName_1426_);
v___x_1440_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1426_, v_env_1430_, v___x_1437_, v___x_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref(v___x_1440_);
lean_inc(v_a_1441_);
v___x_1442_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1426_, v_a_1441_, v_a_1427_);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1451_);
v___x_1444_ = v___x_1442_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v___x_1442_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_a_1441_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_declName_1426_);
v_a_1452_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1440_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1440_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1460_, v_a_1461_);
lean_dec(v_a_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1464_, v_a_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1478_, lean_object* v_localInsts_1479_, lean_object* v_x_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1478_, v_localInsts_1479_, v_x_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1486_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1486_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1503_, lean_object* v_localInsts_1504_, lean_object* v_x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1503_, v_localInsts_1504_, v_x_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1512_, lean_object* v_lctx_1513_, lean_object* v_localInsts_1514_, lean_object* v_x_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1513_, v_localInsts_1514_, v_x_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_lctx_1523_, lean_object* v_localInsts_1524_, lean_object* v_x_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1522_, v_lctx_1523_, v_localInsts_1524_, v_x_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1535_, lean_object* v_as_x27_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
if (lean_obj_tag(v_as_x27_1536_) == 0)
{
lean_object* v___x_1543_; 
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v_declName_1535_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_b_1537_);
return v___x_1543_;
}
else
{
lean_object* v_head_1544_; lean_object* v_tail_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v_b_1537_);
v_head_1544_ = lean_ctor_get(v_as_x27_1536_, 0);
v_tail_1545_ = lean_ctor_get(v_as_x27_1536_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_as_x27_1536_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1547_ = v_as_x27_1536_;
v_isShared_1548_ = v_isSharedCheck_1576_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_tail_1545_);
lean_inc(v_head_1544_);
lean_dec(v_as_x27_1536_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1576_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; 
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v_declName_1535_);
v___x_1549_ = lean_apply_6(v_head_1544_, v_declName_1535_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, lean_box(0));
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = lean_box(0);
if (lean_obj_tag(v_a_1550_) == 1)
{
lean_object* v_val_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_tail_1545_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
v_val_1552_ = lean_ctor_get(v_a_1550_, 0);
lean_inc(v_val_1552_);
v___x_1553_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1535_, v_val_1552_, v___y_1541_);
lean_dec(v___y_1541_);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v___x_1553_, 0);
lean_dec(v_unused_1565_);
v___x_1555_ = v___x_1553_;
v_isShared_1556_ = v_isSharedCheck_1564_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v___x_1553_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1564_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1557_, 0, v_a_1550_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 0);
lean_ctor_set(v___x_1547_, 1, v___x_1551_);
lean_ctor_set(v___x_1547_, 0, v___x_1557_);
v___x_1559_ = v___x_1547_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___x_1551_);
v___x_1559_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1559_);
v___x_1561_ = v___x_1555_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
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
else
{
lean_object* v___x_1566_; 
lean_dec(v_a_1550_);
lean_del_object(v___x_1547_);
v___x_1566_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1536_ = v_tail_1545_;
v_b_1537_ = v___x_1566_;
goto _start;
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_del_object(v___x_1547_);
lean_dec(v_tail_1545_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v_declName_1535_);
v_a_1568_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1549_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1549_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1577_, lean_object* v_as_x27_1578_, lean_object* v_b_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1577_, v_as_x27_1578_, v_b_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v_declName_1586_);
v___x_1592_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1630_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1630_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1630_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_unbox(v_a_1593_);
lean_dec(v_a_1593_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v_declName_1586_);
v___x_1598_ = lean_box(0);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
lean_object* v___x_1602_; 
lean_del_object(v___x_1595_);
lean_inc(v_declName_1586_);
v___x_1602_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1586_, v___y_1590_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
if (lean_obj_tag(v_a_1603_) == 1)
{
lean_dec_ref(v_a_1603_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v_declName_1586_);
return v___x_1602_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_a_1603_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1605_ = lean_st_ref_get(v___x_1604_);
v___x_1606_ = lean_box(0);
v___x_1607_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1608_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1586_, v___x_1605_, v___x_1607_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1621_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1621_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1621_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_fst_1613_; 
v_fst_1613_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_fst_1613_);
lean_dec(v_a_1609_);
if (lean_obj_tag(v_fst_1613_) == 0)
{
lean_object* v___x_1615_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1606_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1606_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
else
{
lean_object* v_val_1617_; lean_object* v___x_1619_; 
v_val_1617_ = lean_ctor_get(v_fst_1613_, 0);
lean_inc(v_val_1617_);
lean_dec_ref(v_fst_1613_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v_val_1617_);
v___x_1619_ = v___x_1611_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_val_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1608_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1608_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
else
{
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v_declName_1586_);
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v_declName_1586_);
v_a_1631_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1592_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1592_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v_res_1645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1649_ = lean_box(1);
v___x_1650_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1651_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v___x_1650_);
lean_ctor_set(v___x_1652_, 2, v___x_1649_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___f_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___f_1661_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1661_, 0, v_declName_1655_);
v___x_1662_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1663_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1664_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1662_, v___x_1663_, v___f_1661_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1672_, lean_object* v_as_1673_, lean_object* v_as_x27_1674_, lean_object* v_b_1675_, lean_object* v_a_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1672_, v_as_x27_1674_, v_b_1675_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1683_, lean_object* v_as_1684_, lean_object* v_as_x27_1685_, lean_object* v_b_1686_, lean_object* v_a_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1683_, v_as_1684_, v_as_x27_1685_, v_b_1686_, v_a_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v_as_1684_);
return v_res_1693_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(lean_object* v_opts_1694_, lean_object* v_opt_1695_){
_start:
{
lean_object* v_name_1696_; lean_object* v_defValue_1697_; lean_object* v_map_1698_; lean_object* v___x_1699_; 
v_name_1696_ = lean_ctor_get(v_opt_1695_, 0);
v_defValue_1697_ = lean_ctor_get(v_opt_1695_, 1);
v_map_1698_ = lean_ctor_get(v_opts_1694_, 0);
v___x_1699_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1698_, v_name_1696_);
if (lean_obj_tag(v___x_1699_) == 0)
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_unbox(v_defValue_1697_);
return v___x_1700_;
}
else
{
lean_object* v_val_1701_; 
v_val_1701_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_val_1701_);
lean_dec_ref(v___x_1699_);
if (lean_obj_tag(v_val_1701_) == 1)
{
uint8_t v_v_1702_; 
v_v_1702_ = lean_ctor_get_uint8(v_val_1701_, 0);
lean_dec_ref(v_val_1701_);
return v_v_1702_;
}
else
{
uint8_t v___x_1703_; 
lean_dec(v_val_1701_);
v___x_1703_ = lean_unbox(v_defValue_1697_);
return v___x_1703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1___boxed(lean_object* v_opts_1704_, lean_object* v_opt_1705_){
_start:
{
uint8_t v_res_1706_; lean_object* v_r_1707_; 
v_res_1706_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_1704_, v_opt_1705_);
lean_dec_ref(v_opt_1705_);
lean_dec_ref(v_opts_1704_);
v_r_1707_ = lean_box(v_res_1706_);
return v_r_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(lean_object* v_opts_1708_, lean_object* v_opt_1709_){
_start:
{
lean_object* v_name_1710_; lean_object* v_defValue_1711_; lean_object* v_map_1712_; lean_object* v___x_1713_; 
v_name_1710_ = lean_ctor_get(v_opt_1709_, 0);
v_defValue_1711_ = lean_ctor_get(v_opt_1709_, 1);
v_map_1712_ = lean_ctor_get(v_opts_1708_, 0);
v___x_1713_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1712_, v_name_1710_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_inc(v_defValue_1711_);
return v_defValue_1711_;
}
else
{
lean_object* v_val_1714_; 
v_val_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_val_1714_);
lean_dec_ref(v___x_1713_);
if (lean_obj_tag(v_val_1714_) == 3)
{
lean_object* v_v_1715_; 
v_v_1715_ = lean_ctor_get(v_val_1714_, 0);
lean_inc(v_v_1715_);
lean_dec_ref(v_val_1714_);
return v_v_1715_;
}
else
{
lean_dec(v_val_1714_);
lean_inc(v_defValue_1711_);
return v_defValue_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2___boxed(lean_object* v_opts_1716_, lean_object* v_opt_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_1716_, v_opt_1717_);
lean_dec_ref(v_opt_1717_);
lean_dec_ref(v_opts_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(lean_object* v_o_1722_, lean_object* v_k_1723_, uint8_t v_v_1724_){
_start:
{
lean_object* v_map_1725_; uint8_t v_hasTrace_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1740_; 
v_map_1725_ = lean_ctor_get(v_o_1722_, 0);
v_hasTrace_1726_ = lean_ctor_get_uint8(v_o_1722_, sizeof(void*)*1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_o_1722_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1728_ = v_o_1722_;
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_map_1725_);
lean_dec(v_o_1722_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1730_, 0, v_v_1724_);
lean_inc(v_k_1723_);
v___x_1731_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1723_, v___x_1730_, v_map_1725_);
if (v_hasTrace_1726_ == 0)
{
lean_object* v___x_1732_; uint8_t v___x_1733_; lean_object* v___x_1735_; 
v___x_1732_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1733_ = l_Lean_Name_isPrefixOf(v___x_1732_, v_k_1723_);
lean_dec(v_k_1723_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1731_);
v___x_1735_ = v___x_1728_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1731_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*1, v___x_1733_);
return v___x_1735_;
}
}
else
{
lean_object* v___x_1738_; 
lean_dec(v_k_1723_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1731_);
v___x_1738_ = v___x_1728_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*1, v_hasTrace_1726_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___boxed(lean_object* v_o_1741_, lean_object* v_k_1742_, lean_object* v_v_1743_){
_start:
{
uint8_t v_v_boxed_1744_; lean_object* v_res_1745_; 
v_v_boxed_1744_ = lean_unbox(v_v_1743_);
v_res_1745_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_o_1741_, v_k_1742_, v_v_boxed_1744_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(lean_object* v_opts_1746_, lean_object* v_opt_1747_, uint8_t v_val_1748_){
_start:
{
lean_object* v_name_1749_; lean_object* v___x_1750_; 
v_name_1749_ = lean_ctor_get(v_opt_1747_, 0);
lean_inc(v_name_1749_);
lean_dec_ref(v_opt_1747_);
v___x_1750_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_opts_1746_, v_name_1749_, v_val_1748_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object* v_opts_1751_, lean_object* v_opt_1752_, lean_object* v_val_1753_){
_start:
{
uint8_t v_val_boxed_1754_; lean_object* v_res_1755_; 
v_val_boxed_1754_ = lean_unbox(v_val_1753_);
v_res_1755_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_opts_1751_, v_opt_1752_, v_val_boxed_1754_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(lean_object* v_as_1756_, size_t v_i_1757_, size_t v_stop_1758_, lean_object* v_b_1759_){
_start:
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_eq(v_i_1757_, v_stop_1758_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v_defValue_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; size_t v___x_1765_; size_t v___x_1766_; 
v___x_1761_ = lean_array_uget_borrowed(v_as_1756_, v_i_1757_);
v_defValue_1762_ = lean_ctor_get(v___x_1761_, 1);
v___x_1763_ = lean_unbox(v_defValue_1762_);
lean_inc(v___x_1761_);
v___x_1764_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_b_1759_, v___x_1761_, v___x_1763_);
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_add(v_i_1757_, v___x_1765_);
v_i_1757_ = v___x_1766_;
v_b_1759_ = v___x_1764_;
goto _start;
}
else
{
return v_b_1759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3___boxed(lean_object* v_as_1768_, lean_object* v_i_1769_, lean_object* v_stop_1770_, lean_object* v_b_1771_){
_start:
{
size_t v_i_boxed_1772_; size_t v_stop_boxed_1773_; lean_object* v_res_1774_; 
v_i_boxed_1772_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_stop_boxed_1773_ = lean_unbox_usize(v_stop_1770_);
lean_dec(v_stop_1770_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v_as_1768_, v_i_boxed_1772_, v_stop_boxed_1773_, v_b_1771_);
lean_dec_ref(v_as_1768_);
return v_res_1774_;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1776_ = lean_array_get_size(v___x_1775_);
return v___x_1776_;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1778_ = lean_nat_dec_le(v___x_1777_, v___x_1777_);
return v___x_1778_;
}
}
static size_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1779_; size_t v___x_1780_; 
v___x_1779_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1780_ = lean_usize_of_nat(v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object* v_declName_1781_, lean_object* v___x_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___y_1789_; uint8_t v___y_1790_; lean_object* v_fileName_1791_; lean_object* v_fileMap_1792_; lean_object* v_currRecDepth_1793_; lean_object* v_ref_1794_; lean_object* v_currNamespace_1795_; lean_object* v_openDecls_1796_; lean_object* v_initHeartbeats_1797_; lean_object* v_maxHeartbeats_1798_; lean_object* v_quotContext_1799_; lean_object* v_currMacroScope_1800_; lean_object* v_cancelTk_x3f_1801_; uint8_t v_suppressElabErrors_1802_; lean_object* v_inheritedTraceOptions_1803_; lean_object* v___y_1804_; lean_object* v___x_1809_; lean_object* v_fileName_1810_; lean_object* v_fileMap_1811_; lean_object* v_options_1812_; lean_object* v_currRecDepth_1813_; lean_object* v_ref_1814_; lean_object* v_currNamespace_1815_; lean_object* v_openDecls_1816_; lean_object* v_initHeartbeats_1817_; lean_object* v_maxHeartbeats_1818_; lean_object* v_quotContext_1819_; lean_object* v_currMacroScope_1820_; lean_object* v_cancelTk_x3f_1821_; uint8_t v_suppressElabErrors_1822_; lean_object* v_inheritedTraceOptions_1823_; lean_object* v___y_1825_; uint8_t v___y_1826_; uint8_t v___y_1827_; lean_object* v___y_1849_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1809_ = lean_st_ref_get(v___y_1786_);
v_fileName_1810_ = lean_ctor_get(v___y_1785_, 0);
lean_inc_ref(v_fileName_1810_);
v_fileMap_1811_ = lean_ctor_get(v___y_1785_, 1);
lean_inc_ref(v_fileMap_1811_);
v_options_1812_ = lean_ctor_get(v___y_1785_, 2);
lean_inc_ref(v_options_1812_);
v_currRecDepth_1813_ = lean_ctor_get(v___y_1785_, 3);
lean_inc(v_currRecDepth_1813_);
v_ref_1814_ = lean_ctor_get(v___y_1785_, 5);
lean_inc(v_ref_1814_);
v_currNamespace_1815_ = lean_ctor_get(v___y_1785_, 6);
lean_inc(v_currNamespace_1815_);
v_openDecls_1816_ = lean_ctor_get(v___y_1785_, 7);
lean_inc(v_openDecls_1816_);
v_initHeartbeats_1817_ = lean_ctor_get(v___y_1785_, 8);
lean_inc(v_initHeartbeats_1817_);
v_maxHeartbeats_1818_ = lean_ctor_get(v___y_1785_, 9);
lean_inc(v_maxHeartbeats_1818_);
v_quotContext_1819_ = lean_ctor_get(v___y_1785_, 10);
lean_inc(v_quotContext_1819_);
v_currMacroScope_1820_ = lean_ctor_get(v___y_1785_, 11);
lean_inc(v_currMacroScope_1820_);
v_cancelTk_x3f_1821_ = lean_ctor_get(v___y_1785_, 12);
lean_inc(v_cancelTk_x3f_1821_);
v_suppressElabErrors_1822_ = lean_ctor_get_uint8(v___y_1785_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1823_ = lean_ctor_get(v___y_1785_, 13);
lean_inc_ref(v_inheritedTraceOptions_1823_);
lean_dec_ref(v___y_1785_);
v___x_1854_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1855_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1856_ = lean_nat_dec_lt(v___x_1782_, v___x_1855_);
if (v___x_1856_ == 0)
{
v___y_1849_ = v_options_1812_;
goto v___jp_1848_;
}
else
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_uint8_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1);
if (v___x_1857_ == 0)
{
if (v___x_1856_ == 0)
{
v___y_1849_ = v_options_1812_;
goto v___jp_1848_;
}
else
{
size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1854_, v___x_1858_, v___x_1859_, v_options_1812_);
v___y_1849_ = v___x_1860_;
goto v___jp_1848_;
}
}
else
{
size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = ((size_t)0ULL);
v___x_1862_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1854_, v___x_1861_, v___x_1862_, v_options_1812_);
v___y_1849_ = v___x_1863_;
goto v___jp_1848_;
}
}
v___jp_1788_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = l_Lean_maxRecDepth;
v___x_1806_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v___y_1789_, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1807_, 0, v_fileName_1791_);
lean_ctor_set(v___x_1807_, 1, v_fileMap_1792_);
lean_ctor_set(v___x_1807_, 2, v___y_1789_);
lean_ctor_set(v___x_1807_, 3, v_currRecDepth_1793_);
lean_ctor_set(v___x_1807_, 4, v___x_1806_);
lean_ctor_set(v___x_1807_, 5, v_ref_1794_);
lean_ctor_set(v___x_1807_, 6, v_currNamespace_1795_);
lean_ctor_set(v___x_1807_, 7, v_openDecls_1796_);
lean_ctor_set(v___x_1807_, 8, v_initHeartbeats_1797_);
lean_ctor_set(v___x_1807_, 9, v_maxHeartbeats_1798_);
lean_ctor_set(v___x_1807_, 10, v_quotContext_1799_);
lean_ctor_set(v___x_1807_, 11, v_currMacroScope_1800_);
lean_ctor_set(v___x_1807_, 12, v_cancelTk_x3f_1801_);
lean_ctor_set(v___x_1807_, 13, v_inheritedTraceOptions_1803_);
lean_ctor_set_uint8(v___x_1807_, sizeof(void*)*14, v___y_1790_);
lean_ctor_set_uint8(v___x_1807_, sizeof(void*)*14 + 1, v_suppressElabErrors_1802_);
v___x_1808_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1781_, v___y_1783_, v___y_1784_, v___x_1807_, v___y_1804_);
return v___x_1808_;
}
v___jp_1824_:
{
if (v___y_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v_env_1829_; lean_object* v_nextMacroScope_1830_; lean_object* v_ngen_1831_; lean_object* v_auxDeclNGen_1832_; lean_object* v_traceState_1833_; lean_object* v_messages_1834_; lean_object* v_infoState_1835_; lean_object* v_snapshotTasks_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1846_; 
v___x_1828_ = lean_st_ref_take(v___y_1786_);
v_env_1829_ = lean_ctor_get(v___x_1828_, 0);
v_nextMacroScope_1830_ = lean_ctor_get(v___x_1828_, 1);
v_ngen_1831_ = lean_ctor_get(v___x_1828_, 2);
v_auxDeclNGen_1832_ = lean_ctor_get(v___x_1828_, 3);
v_traceState_1833_ = lean_ctor_get(v___x_1828_, 4);
v_messages_1834_ = lean_ctor_get(v___x_1828_, 6);
v_infoState_1835_ = lean_ctor_get(v___x_1828_, 7);
v_snapshotTasks_1836_ = lean_ctor_get(v___x_1828_, 8);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v___x_1828_, 5);
lean_dec(v_unused_1847_);
v___x_1838_ = v___x_1828_;
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_snapshotTasks_1836_);
lean_inc(v_infoState_1835_);
lean_inc(v_messages_1834_);
lean_inc(v_traceState_1833_);
lean_inc(v_auxDeclNGen_1832_);
lean_inc(v_ngen_1831_);
lean_inc(v_nextMacroScope_1830_);
lean_inc(v_env_1829_);
lean_dec(v___x_1828_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = l_Lean_Kernel_enableDiag(v_env_1829_, v___y_1826_);
v___x_1841_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 5, v___x_1841_);
lean_ctor_set(v___x_1838_, 0, v___x_1840_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_nextMacroScope_1830_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_ngen_1831_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_auxDeclNGen_1832_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_traceState_1833_);
lean_ctor_set(v_reuseFailAlloc_1845_, 5, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_messages_1834_);
lean_ctor_set(v_reuseFailAlloc_1845_, 7, v_infoState_1835_);
lean_ctor_set(v_reuseFailAlloc_1845_, 8, v_snapshotTasks_1836_);
v___x_1843_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_st_ref_set(v___y_1786_, v___x_1843_);
v___y_1789_ = v___y_1825_;
v___y_1790_ = v___y_1826_;
v_fileName_1791_ = v_fileName_1810_;
v_fileMap_1792_ = v_fileMap_1811_;
v_currRecDepth_1793_ = v_currRecDepth_1813_;
v_ref_1794_ = v_ref_1814_;
v_currNamespace_1795_ = v_currNamespace_1815_;
v_openDecls_1796_ = v_openDecls_1816_;
v_initHeartbeats_1797_ = v_initHeartbeats_1817_;
v_maxHeartbeats_1798_ = v_maxHeartbeats_1818_;
v_quotContext_1799_ = v_quotContext_1819_;
v_currMacroScope_1800_ = v_currMacroScope_1820_;
v_cancelTk_x3f_1801_ = v_cancelTk_x3f_1821_;
v_suppressElabErrors_1802_ = v_suppressElabErrors_1822_;
v_inheritedTraceOptions_1803_ = v_inheritedTraceOptions_1823_;
v___y_1804_ = v___y_1786_;
goto v___jp_1788_;
}
}
}
else
{
v___y_1789_ = v___y_1825_;
v___y_1790_ = v___y_1826_;
v_fileName_1791_ = v_fileName_1810_;
v_fileMap_1792_ = v_fileMap_1811_;
v_currRecDepth_1793_ = v_currRecDepth_1813_;
v_ref_1794_ = v_ref_1814_;
v_currNamespace_1795_ = v_currNamespace_1815_;
v_openDecls_1796_ = v_openDecls_1816_;
v_initHeartbeats_1797_ = v_initHeartbeats_1817_;
v_maxHeartbeats_1798_ = v_maxHeartbeats_1818_;
v_quotContext_1799_ = v_quotContext_1819_;
v_currMacroScope_1800_ = v_currMacroScope_1820_;
v_cancelTk_x3f_1801_ = v_cancelTk_x3f_1821_;
v_suppressElabErrors_1802_ = v_suppressElabErrors_1822_;
v_inheritedTraceOptions_1803_ = v_inheritedTraceOptions_1823_;
v___y_1804_ = v___y_1786_;
goto v___jp_1788_;
}
}
v___jp_1848_:
{
lean_object* v_env_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; uint8_t v___x_1853_; 
v_env_1850_ = lean_ctor_get(v___x_1809_, 0);
lean_inc_ref(v_env_1850_);
lean_dec(v___x_1809_);
v___x_1851_ = l_Lean_diagnostics;
v___x_1852_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___y_1849_, v___x_1851_);
v___x_1853_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1850_);
lean_dec_ref(v_env_1850_);
if (v___x_1853_ == 0)
{
if (v___x_1852_ == 0)
{
v___y_1789_ = v___y_1849_;
v___y_1790_ = v___x_1852_;
v_fileName_1791_ = v_fileName_1810_;
v_fileMap_1792_ = v_fileMap_1811_;
v_currRecDepth_1793_ = v_currRecDepth_1813_;
v_ref_1794_ = v_ref_1814_;
v_currNamespace_1795_ = v_currNamespace_1815_;
v_openDecls_1796_ = v_openDecls_1816_;
v_initHeartbeats_1797_ = v_initHeartbeats_1817_;
v_maxHeartbeats_1798_ = v_maxHeartbeats_1818_;
v_quotContext_1799_ = v_quotContext_1819_;
v_currMacroScope_1800_ = v_currMacroScope_1820_;
v_cancelTk_x3f_1801_ = v_cancelTk_x3f_1821_;
v_suppressElabErrors_1802_ = v_suppressElabErrors_1822_;
v_inheritedTraceOptions_1803_ = v_inheritedTraceOptions_1823_;
v___y_1804_ = v___y_1786_;
goto v___jp_1788_;
}
else
{
v___y_1825_ = v___y_1849_;
v___y_1826_ = v___x_1852_;
v___y_1827_ = v___x_1853_;
goto v___jp_1824_;
}
}
else
{
v___y_1825_ = v___y_1849_;
v___y_1826_ = v___x_1852_;
v___y_1827_ = v___x_1852_;
goto v___jp_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object* v_declName_1864_, lean_object* v___x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Meta_getEqnsFor_x3f___lam__0(v_declName_1864_, v___x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___x_1865_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___f_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1878_ = lean_unsigned_to_nat(32u);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1878_);
lean_dec_ref(v___x_1879_);
v___x_1880_ = lean_unsigned_to_nat(0u);
v___f_1881_ = lean_alloc_closure((void*)(l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1881_, 0, v_declName_1872_);
lean_closure_set(v___f_1881_, 1, v___x_1880_);
v___x_1882_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1884_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1882_, v___x_1883_, v___f_1881_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(lean_object* v_cls_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_options_1895_; uint8_t v_hasTrace_1896_; 
v_options_1895_ = lean_ctor_get(v___y_1893_, 2);
v_hasTrace_1896_ = lean_ctor_get_uint8(v_options_1895_, sizeof(void*)*1);
if (v_hasTrace_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v_cls_1892_);
v___x_1897_ = lean_box(v_hasTrace_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
else
{
lean_object* v_inheritedTraceOptions_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_inheritedTraceOptions_1899_ = lean_ctor_get(v___y_1893_, 13);
v___x_1900_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1901_ = l_Lean_Name_append(v___x_1900_, v_cls_1892_);
v___x_1902_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1899_, v_options_1895_, v___x_1901_);
lean_dec(v___x_1901_);
v___x_1903_ = lean_box(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg___boxed(lean_object* v_cls_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v_cls_1905_, v___y_1906_);
lean_dec_ref(v___y_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1(lean_object* v_cls_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v_cls_1909_, v___y_1912_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___boxed(lean_object* v_cls_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1(v_cls_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(lean_object* v_msgData_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; lean_object* v_env_1930_; lean_object* v___x_1931_; lean_object* v_mctx_1932_; lean_object* v_lctx_1933_; lean_object* v_options_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1929_ = lean_st_ref_get(v___y_1927_);
v_env_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc_ref(v_env_1930_);
lean_dec(v___x_1929_);
v___x_1931_ = lean_st_ref_get(v___y_1925_);
v_mctx_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc_ref(v_mctx_1932_);
lean_dec(v___x_1931_);
v_lctx_1933_ = lean_ctor_get(v___y_1924_, 2);
v_options_1934_ = lean_ctor_get(v___y_1926_, 2);
lean_inc_ref(v_options_1934_);
lean_inc_ref(v_lctx_1933_);
v___x_1935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1935_, 0, v_env_1930_);
lean_ctor_set(v___x_1935_, 1, v_mctx_1932_);
lean_ctor_set(v___x_1935_, 2, v_lctx_1933_);
lean_ctor_set(v___x_1935_, 3, v_options_1934_);
v___x_1936_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v_msgData_1923_);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2___boxed(lean_object* v_msgData_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msgData_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
return v_res_1944_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1945_; double v___x_1946_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_float_of_nat(v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(lean_object* v_cls_1950_, lean_object* v_msg_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_ref_1957_; lean_object* v___x_1958_; lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_2003_; 
v_ref_1957_ = lean_ctor_get(v___y_1954_, 5);
v___x_1958_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msg_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_2003_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_2003_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v_traceState_1964_; lean_object* v_env_1965_; lean_object* v_nextMacroScope_1966_; lean_object* v_ngen_1967_; lean_object* v_auxDeclNGen_1968_; lean_object* v_cache_1969_; lean_object* v_messages_1970_; lean_object* v_infoState_1971_; lean_object* v_snapshotTasks_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2002_; 
v___x_1963_ = lean_st_ref_take(v___y_1955_);
v_traceState_1964_ = lean_ctor_get(v___x_1963_, 4);
v_env_1965_ = lean_ctor_get(v___x_1963_, 0);
v_nextMacroScope_1966_ = lean_ctor_get(v___x_1963_, 1);
v_ngen_1967_ = lean_ctor_get(v___x_1963_, 2);
v_auxDeclNGen_1968_ = lean_ctor_get(v___x_1963_, 3);
v_cache_1969_ = lean_ctor_get(v___x_1963_, 5);
v_messages_1970_ = lean_ctor_get(v___x_1963_, 6);
v_infoState_1971_ = lean_ctor_get(v___x_1963_, 7);
v_snapshotTasks_1972_ = lean_ctor_get(v___x_1963_, 8);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1974_ = v___x_1963_;
v_isShared_1975_ = v_isSharedCheck_2002_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_snapshotTasks_1972_);
lean_inc(v_infoState_1971_);
lean_inc(v_messages_1970_);
lean_inc(v_cache_1969_);
lean_inc(v_traceState_1964_);
lean_inc(v_auxDeclNGen_1968_);
lean_inc(v_ngen_1967_);
lean_inc(v_nextMacroScope_1966_);
lean_inc(v_env_1965_);
lean_dec(v___x_1963_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2002_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
uint64_t v_tid_1976_; lean_object* v_traces_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2001_; 
v_tid_1976_ = lean_ctor_get_uint64(v_traceState_1964_, sizeof(void*)*1);
v_traces_1977_ = lean_ctor_get(v_traceState_1964_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_traceState_1964_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1979_ = v_traceState_1964_;
v_isShared_1980_ = v_isSharedCheck_2001_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_traces_1977_);
lean_dec(v_traceState_1964_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2001_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; double v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0);
v___x_1983_ = 0;
v___x_1984_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1));
v___x_1985_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1985_, 0, v_cls_1950_);
lean_ctor_set(v___x_1985_, 1, v___x_1981_);
lean_ctor_set(v___x_1985_, 2, v___x_1984_);
lean_ctor_set_float(v___x_1985_, sizeof(void*)*3, v___x_1982_);
lean_ctor_set_float(v___x_1985_, sizeof(void*)*3 + 8, v___x_1982_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*3 + 16, v___x_1983_);
v___x_1986_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__2));
v___x_1987_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set(v___x_1987_, 1, v_a_1959_);
lean_ctor_set(v___x_1987_, 2, v___x_1986_);
lean_inc(v_ref_1957_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_ref_1957_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_PersistentArray_push___redArg(v_traces_1977_, v___x_1988_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1989_);
v___x_1991_ = v___x_1979_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1989_);
lean_ctor_set_uint64(v_reuseFailAlloc_2000_, sizeof(void*)*1, v_tid_1976_);
v___x_1991_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 4, v___x_1991_);
v___x_1993_ = v___x_1974_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_env_1965_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_nextMacroScope_1966_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_ngen_1967_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_auxDeclNGen_1968_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1999_, 5, v_cache_1969_);
lean_ctor_set(v_reuseFailAlloc_1999_, 6, v_messages_1970_);
lean_ctor_set(v_reuseFailAlloc_1999_, 7, v_infoState_1971_);
lean_ctor_set(v_reuseFailAlloc_1999_, 8, v_snapshotTasks_1972_);
v___x_1993_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1994_ = lean_st_ref_set(v___y_1955_, v___x_1993_);
v___x_1995_ = lean_box(0);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1995_);
v___x_1997_ = v___x_1961_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___boxed(lean_object* v_cls_2004_, lean_object* v_msg_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(v_cls_2004_, v_msg_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(lean_object* v___x_2012_, lean_object* v_as_2013_, size_t v_i_2014_, size_t v_stop_2015_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_usize_dec_eq(v_i_2014_, v_stop_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v_defValue_2018_; uint8_t v___x_2019_; uint8_t v___y_2025_; uint8_t v___x_2026_; 
v___x_2017_ = lean_array_uget_borrowed(v_as_2013_, v_i_2014_);
v_defValue_2018_ = lean_ctor_get(v___x_2017_, 1);
v___x_2019_ = 1;
v___x_2026_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___x_2012_, v___x_2017_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_unbox(v_defValue_2018_);
if (v___x_2027_ == 0)
{
goto v___jp_2020_;
}
else
{
v___y_2025_ = v___x_2026_;
goto v___jp_2024_;
}
}
else
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_unbox(v_defValue_2018_);
v___y_2025_ = v___x_2028_;
goto v___jp_2024_;
}
v___jp_2020_:
{
if (v___x_2016_ == 0)
{
size_t v___x_2021_; size_t v___x_2022_; 
v___x_2021_ = ((size_t)1ULL);
v___x_2022_ = lean_usize_add(v_i_2014_, v___x_2021_);
v_i_2014_ = v___x_2022_;
goto _start;
}
else
{
return v___x_2019_;
}
}
v___jp_2024_:
{
if (v___y_2025_ == 0)
{
return v___x_2019_;
}
else
{
goto v___jp_2020_;
}
}
}
else
{
uint8_t v___x_2029_; 
v___x_2029_ = 0;
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object* v___x_2030_, lean_object* v_as_2031_, lean_object* v_i_2032_, lean_object* v_stop_2033_){
_start:
{
size_t v_i_boxed_2034_; size_t v_stop_boxed_2035_; uint8_t v_res_2036_; lean_object* v_r_2037_; 
v_i_boxed_2034_ = lean_unbox_usize(v_i_2032_);
lean_dec(v_i_2032_);
v_stop_boxed_2035_ = lean_unbox_usize(v_stop_2033_);
lean_dec(v_stop_2033_);
v_res_2036_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v___x_2030_, v_as_2031_, v_i_boxed_2034_, v_stop_boxed_2035_);
lean_dec_ref(v_as_2031_);
lean_dec_ref(v___x_2030_);
v_r_2037_ = lean_box(v_res_2036_);
return v_r_2037_;
}
}
static uint8_t _init_l_Lean_Meta_generateEagerEqns___closed__0(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2038_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = lean_nat_dec_lt(v___x_2039_, v___x_2038_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__5(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__4));
v___x_2049_ = l_Lean_stringToMessageData(v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object* v_declName_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = l_Lean_Meta_eqnAffectingOptions;
v___x_2083_ = lean_uint8_once(&l_Lean_Meta_generateEagerEqns___closed__0, &l_Lean_Meta_generateEagerEqns___closed__0_once, _init_l_Lean_Meta_generateEagerEqns___closed__0);
if (v___x_2083_ == 0)
{
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_declName_2050_);
goto v___jp_2056_;
}
else
{
if (v___x_2083_ == 0)
{
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_declName_2050_);
goto v___jp_2056_;
}
else
{
lean_object* v_options_2084_; size_t v___x_2085_; size_t v___x_2086_; uint8_t v___x_2087_; 
v_options_2084_ = lean_ctor_get(v_a_2053_, 2);
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v_options_2084_, v___x_2082_, v___x_2085_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_declName_2050_);
goto v___jp_2056_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_a_2090_; uint8_t v___x_2091_; 
v___x_2088_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_2089_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_generateEagerEqns_spec__1___redArg(v___x_2088_, v_a_2053_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = lean_unbox(v_a_2090_);
lean_dec(v_a_2090_);
if (v___x_2091_ == 0)
{
v___y_2060_ = v_a_2051_;
v___y_2061_ = v_a_2052_;
v___y_2062_ = v_a_2053_;
v___y_2063_ = v_a_2054_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2092_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__5, &l_Lean_Meta_generateEagerEqns___closed__5_once, _init_l_Lean_Meta_generateEagerEqns___closed__5);
lean_inc(v_declName_2050_);
v___x_2093_ = l_Lean_MessageData_ofName(v_declName_2050_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2(v___x_2088_, v___x_2094_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref(v___x_2095_);
v___y_2060_ = v_a_2051_;
v___y_2061_ = v_a_2052_;
v___y_2062_ = v_a_2053_;
v___y_2063_ = v_a_2054_;
goto v___jp_2059_;
}
else
{
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_declName_2050_);
return v___x_2095_;
}
}
}
}
}
v___jp_2056_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
v___jp_2059_:
{
lean_object* v___x_2064_; 
v___x_2064_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_2050_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2072_; 
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2064_, 0);
lean_dec(v_unused_2073_);
v___x_2066_ = v___x_2064_;
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v___x_2064_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_box(0);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_a_2074_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2064_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2064_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___boxed(lean_object* v_declName_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Meta_generateEagerEqns(v_declName_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_st_mk_ref(v___x_2104_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2128_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2128_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2128_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
uint8_t v___x_2116_; 
v___x_2116_ = lean_unbox(v_a_2112_);
lean_dec(v_a_2112_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_dec_ref(v_f_2109_);
v___x_2117_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 1);
lean_ctor_set(v___x_2114_, 0, v___x_2117_);
v___x_2119_ = v___x_2114_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2121_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2122_ = lean_st_ref_take(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2123_, 0, v_f_2109_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = lean_st_ref_set(v___x_2121_, v___x_2123_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2124_);
v___x_2126_ = v___x_2114_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
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
lean_dec_ref(v_f_2109_);
v_a_2129_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2111_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2111_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2137_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2143_, lean_object* v_as_x27_2144_, lean_object* v_b_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
if (lean_obj_tag(v_as_x27_2144_) == 0)
{
lean_object* v___x_2151_; 
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v_declName_2143_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v_b_2145_);
return v___x_2151_;
}
else
{
lean_object* v_head_2152_; lean_object* v_tail_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v_b_2145_);
v_head_2152_ = lean_ctor_get(v_as_x27_2144_, 0);
v_tail_2153_ = lean_ctor_get(v_as_x27_2144_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_as_x27_2144_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2155_ = v_as_x27_2144_;
v_isShared_2156_ = v_isSharedCheck_2181_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_tail_2153_);
lean_inc(v_head_2152_);
lean_dec(v_as_x27_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2181_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; 
lean_inc(v___y_2149_);
lean_inc_ref(v___y_2148_);
lean_inc(v___y_2147_);
lean_inc_ref(v___y_2146_);
lean_inc(v_declName_2143_);
v___x_2157_ = lean_apply_6(v_head_2152_, v_declName_2143_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, lean_box(0));
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2172_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_box(0);
if (lean_obj_tag(v_a_2158_) == 1)
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_dec(v_tail_2153_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v_declName_2143_);
v___x_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_a_2158_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 0);
lean_ctor_set(v___x_2155_, 1, v___x_2162_);
lean_ctor_set(v___x_2155_, 0, v___x_2163_);
v___x_2165_ = v___x_2155_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2162_);
v___x_2165_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2165_);
v___x_2167_ = v___x_2160_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
lean_object* v___x_2170_; 
lean_del_object(v___x_2160_);
lean_dec(v_a_2158_);
lean_del_object(v___x_2155_);
v___x_2170_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2144_ = v_tail_2153_;
v_b_2145_ = v___x_2170_;
goto _start;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_del_object(v___x_2155_);
lean_dec(v_tail_2153_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v_declName_2143_);
v_a_2173_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2157_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2157_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2182_, lean_object* v_as_x27_2183_, lean_object* v_b_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2182_, v_as_x27_2183_, v_b_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2191_, lean_object* v_declName_2192_, uint8_t v_nonRec_2193_, lean_object* v___x_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2203_; lean_object* v_env_2204_; uint8_t v___x_2205_; uint8_t v___x_2206_; 
v___x_2203_ = lean_st_ref_get(v___y_2198_);
v_env_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc_ref(v_env_2204_);
lean_dec(v___x_2203_);
v___x_2205_ = 1;
lean_inc(v___x_2191_);
v___x_2206_ = l_Lean_Environment_contains(v_env_2204_, v___x_2191_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
lean_dec(v___x_2191_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v_declName_2192_);
v___x_2207_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2192_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; uint8_t v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = lean_unbox(v_a_2208_);
lean_dec(v_a_2208_);
if (v___x_2209_ == 0)
{
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v___x_2194_);
lean_dec(v_declName_2192_);
goto v___jp_2200_;
}
else
{
lean_object* v___x_2210_; 
lean_inc(v_declName_2192_);
v___x_2210_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2192_, v___y_2198_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; uint8_t v___x_2212_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2210_);
v___x_2212_ = lean_unbox(v_a_2211_);
lean_dec(v_a_2211_);
if (v___x_2212_ == 0)
{
if (v_nonRec_2193_ == 0)
{
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v___x_2194_);
lean_dec(v_declName_2192_);
goto v___jp_2200_;
}
else
{
lean_object* v___x_2213_; lean_object* v_env_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_st_ref_get(v___y_2198_);
v_env_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc_ref(v_env_2214_);
lean_dec(v___x_2213_);
lean_inc(v_declName_2192_);
v___x_2215_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2214_, v_declName_2192_, v___x_2194_);
v___x_2216_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2192_, v___x_2215_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v___x_2216_;
}
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec_ref(v___x_2194_);
v___x_2217_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2218_ = lean_st_ref_get(v___x_2217_);
v___x_2219_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2220_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2192_, v___x_2218_, v___x_2219_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2230_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2230_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2230_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_fst_2225_; 
v_fst_2225_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_fst_2225_);
lean_dec(v_a_2221_);
if (lean_obj_tag(v_fst_2225_) == 0)
{
lean_del_object(v___x_2223_);
goto v___jp_2200_;
}
else
{
lean_object* v_val_2226_; lean_object* v___x_2228_; 
v_val_2226_ = lean_ctor_get(v_fst_2225_, 0);
lean_inc(v_val_2226_);
lean_dec_ref(v_fst_2225_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v_val_2226_);
v___x_2228_ = v___x_2223_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_val_2226_);
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
v_a_2231_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2220_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2220_);
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
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v___x_2194_);
lean_dec(v_declName_2192_);
v_a_2239_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2210_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2210_);
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
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v___x_2194_);
lean_dec(v_declName_2192_);
v_a_2247_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2207_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2207_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v___x_2194_);
lean_dec(v_declName_2192_);
v___x_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2191_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
v___jp_2200_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2257_, lean_object* v_declName_2258_, lean_object* v_nonRec_2259_, lean_object* v___x_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
uint8_t v_nonRec_boxed_2266_; lean_object* v_res_2267_; 
v_nonRec_boxed_2266_ = lean_unbox(v_nonRec_2259_);
v_res_2267_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2257_, v_declName_2258_, v_nonRec_boxed_2266_, v___x_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_ref_2274_; lean_object* v___x_2275_; lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2284_; 
v_ref_2274_ = lean_ctor_get(v___y_2271_, 5);
v___x_2275_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2_spec__2(v_msg_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
lean_inc(v_ref_2274_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v_ref_2274_);
lean_ctor_set(v___x_2280_, 1, v_a_2276_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 1);
lean_ctor_set(v___x_2278_, 0, v___x_2280_);
v___x_2282_ = v___x_2278_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2292_, uint8_t v_isExporting_2293_, lean_object* v___x_2294_, lean_object* v___y_2295_, lean_object* v___x_2296_, lean_object* v_a_x3f_2297_){
_start:
{
lean_object* v___x_2299_; lean_object* v_env_2300_; lean_object* v_nextMacroScope_2301_; lean_object* v_ngen_2302_; lean_object* v_auxDeclNGen_2303_; lean_object* v_traceState_2304_; lean_object* v_messages_2305_; lean_object* v_infoState_2306_; lean_object* v_snapshotTasks_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2332_; 
v___x_2299_ = lean_st_ref_take(v___y_2292_);
v_env_2300_ = lean_ctor_get(v___x_2299_, 0);
v_nextMacroScope_2301_ = lean_ctor_get(v___x_2299_, 1);
v_ngen_2302_ = lean_ctor_get(v___x_2299_, 2);
v_auxDeclNGen_2303_ = lean_ctor_get(v___x_2299_, 3);
v_traceState_2304_ = lean_ctor_get(v___x_2299_, 4);
v_messages_2305_ = lean_ctor_get(v___x_2299_, 6);
v_infoState_2306_ = lean_ctor_get(v___x_2299_, 7);
v_snapshotTasks_2307_ = lean_ctor_get(v___x_2299_, 8);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2332_ == 0)
{
lean_object* v_unused_2333_; 
v_unused_2333_ = lean_ctor_get(v___x_2299_, 5);
lean_dec(v_unused_2333_);
v___x_2309_ = v___x_2299_;
v_isShared_2310_ = v_isSharedCheck_2332_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_snapshotTasks_2307_);
lean_inc(v_infoState_2306_);
lean_inc(v_messages_2305_);
lean_inc(v_traceState_2304_);
lean_inc(v_auxDeclNGen_2303_);
lean_inc(v_ngen_2302_);
lean_inc(v_nextMacroScope_2301_);
lean_inc(v_env_2300_);
lean_dec(v___x_2299_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2332_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = l_Lean_Environment_setExporting(v_env_2300_, v_isExporting_2293_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 5, v___x_2294_);
lean_ctor_set(v___x_2309_, 0, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_nextMacroScope_2301_);
lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_ngen_2302_);
lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_auxDeclNGen_2303_);
lean_ctor_set(v_reuseFailAlloc_2331_, 4, v_traceState_2304_);
lean_ctor_set(v_reuseFailAlloc_2331_, 5, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2331_, 6, v_messages_2305_);
lean_ctor_set(v_reuseFailAlloc_2331_, 7, v_infoState_2306_);
lean_ctor_set(v_reuseFailAlloc_2331_, 8, v_snapshotTasks_2307_);
v___x_2313_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v_mctx_2316_; lean_object* v_zetaDeltaFVarIds_2317_; lean_object* v_postponed_2318_; lean_object* v_diag_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2329_; 
v___x_2314_ = lean_st_ref_set(v___y_2292_, v___x_2313_);
v___x_2315_ = lean_st_ref_take(v___y_2295_);
v_mctx_2316_ = lean_ctor_get(v___x_2315_, 0);
v_zetaDeltaFVarIds_2317_ = lean_ctor_get(v___x_2315_, 2);
v_postponed_2318_ = lean_ctor_get(v___x_2315_, 3);
v_diag_2319_ = lean_ctor_get(v___x_2315_, 4);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2315_, 1);
lean_dec(v_unused_2330_);
v___x_2321_ = v___x_2315_;
v_isShared_2322_ = v_isSharedCheck_2329_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_diag_2319_);
lean_inc(v_postponed_2318_);
lean_inc(v_zetaDeltaFVarIds_2317_);
lean_inc(v_mctx_2316_);
lean_dec(v___x_2315_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2329_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v___x_2296_);
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_mctx_2316_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_zetaDeltaFVarIds_2317_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_postponed_2318_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_diag_2319_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_st_ref_set(v___y_2295_, v___x_2324_);
v___x_2326_ = lean_box(0);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2334_, lean_object* v_isExporting_2335_, lean_object* v___x_2336_, lean_object* v___y_2337_, lean_object* v___x_2338_, lean_object* v_a_x3f_2339_, lean_object* v___y_2340_){
_start:
{
uint8_t v_isExporting_boxed_2341_; lean_object* v_res_2342_; 
v_isExporting_boxed_2341_ = lean_unbox(v_isExporting_2335_);
v_res_2342_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2334_, v_isExporting_boxed_2341_, v___x_2336_, v___y_2337_, v___x_2338_, v_a_x3f_2339_);
lean_dec(v_a_x3f_2339_);
lean_dec(v___y_2337_);
lean_dec(v___y_2334_);
return v_res_2342_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_2344_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
lean_ctor_set(v___x_2344_, 2, v___x_2343_);
lean_ctor_set(v___x_2344_, 3, v___x_2343_);
lean_ctor_set(v___x_2344_, 4, v___x_2343_);
lean_ctor_set(v___x_2344_, 5, v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2345_, uint8_t v_isExporting_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v_env_2353_; uint8_t v_isExporting_2354_; lean_object* v___x_2355_; lean_object* v_env_2356_; lean_object* v_nextMacroScope_2357_; lean_object* v_ngen_2358_; lean_object* v_auxDeclNGen_2359_; lean_object* v_traceState_2360_; lean_object* v_messages_2361_; lean_object* v_infoState_2362_; lean_object* v_snapshotTasks_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2417_; 
v___x_2352_ = lean_st_ref_get(v___y_2350_);
v_env_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_ref(v_env_2353_);
lean_dec(v___x_2352_);
v_isExporting_2354_ = lean_ctor_get_uint8(v_env_2353_, sizeof(void*)*8);
lean_dec_ref(v_env_2353_);
v___x_2355_ = lean_st_ref_take(v___y_2350_);
v_env_2356_ = lean_ctor_get(v___x_2355_, 0);
v_nextMacroScope_2357_ = lean_ctor_get(v___x_2355_, 1);
v_ngen_2358_ = lean_ctor_get(v___x_2355_, 2);
v_auxDeclNGen_2359_ = lean_ctor_get(v___x_2355_, 3);
v_traceState_2360_ = lean_ctor_get(v___x_2355_, 4);
v_messages_2361_ = lean_ctor_get(v___x_2355_, 6);
v_infoState_2362_ = lean_ctor_get(v___x_2355_, 7);
v_snapshotTasks_2363_ = lean_ctor_get(v___x_2355_, 8);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v___x_2355_, 5);
lean_dec(v_unused_2418_);
v___x_2365_ = v___x_2355_;
v_isShared_2366_ = v_isSharedCheck_2417_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_snapshotTasks_2363_);
lean_inc(v_infoState_2362_);
lean_inc(v_messages_2361_);
lean_inc(v_traceState_2360_);
lean_inc(v_auxDeclNGen_2359_);
lean_inc(v_ngen_2358_);
lean_inc(v_nextMacroScope_2357_);
lean_inc(v_env_2356_);
lean_dec(v___x_2355_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2417_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2367_ = l_Lean_Environment_setExporting(v_env_2356_, v_isExporting_2346_);
v___x_2368_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 5, v___x_2368_);
lean_ctor_set(v___x_2365_, 0, v___x_2367_);
v___x_2370_ = v___x_2365_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_nextMacroScope_2357_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_ngen_2358_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v_auxDeclNGen_2359_);
lean_ctor_set(v_reuseFailAlloc_2416_, 4, v_traceState_2360_);
lean_ctor_set(v_reuseFailAlloc_2416_, 5, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2416_, 6, v_messages_2361_);
lean_ctor_set(v_reuseFailAlloc_2416_, 7, v_infoState_2362_);
lean_ctor_set(v_reuseFailAlloc_2416_, 8, v_snapshotTasks_2363_);
v___x_2370_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v_mctx_2373_; lean_object* v_zetaDeltaFVarIds_2374_; lean_object* v_postponed_2375_; lean_object* v_diag_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2414_; 
v___x_2371_ = lean_st_ref_set(v___y_2350_, v___x_2370_);
v___x_2372_ = lean_st_ref_take(v___y_2348_);
v_mctx_2373_ = lean_ctor_get(v___x_2372_, 0);
v_zetaDeltaFVarIds_2374_ = lean_ctor_get(v___x_2372_, 2);
v_postponed_2375_ = lean_ctor_get(v___x_2372_, 3);
v_diag_2376_ = lean_ctor_get(v___x_2372_, 4);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v___x_2372_, 1);
lean_dec(v_unused_2415_);
v___x_2378_ = v___x_2372_;
v_isShared_2379_ = v_isSharedCheck_2414_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_diag_2376_);
lean_inc(v_postponed_2375_);
lean_inc(v_zetaDeltaFVarIds_2374_);
lean_inc(v_mctx_2373_);
lean_dec(v___x_2372_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2414_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2380_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 1, v___x_2380_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_mctx_2373_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_zetaDeltaFVarIds_2374_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_postponed_2375_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v_diag_2376_);
v___x_2382_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; lean_object* v_r_2384_; 
v___x_2383_ = lean_st_ref_set(v___y_2348_, v___x_2382_);
lean_inc(v___y_2350_);
lean_inc(v___y_2348_);
v_r_2384_ = lean_apply_5(v_x_2345_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, lean_box(0));
if (lean_obj_tag(v_r_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2401_; 
v_a_2385_ = lean_ctor_get(v_r_2384_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_r_2384_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2387_ = v_r_2384_;
v_isShared_2388_ = v_isSharedCheck_2401_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v_r_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2401_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
lean_inc(v_a_2385_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 1);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v___x_2391_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2350_, v_isExporting_2354_, v___x_2368_, v___y_2348_, v___x_2380_, v___x_2390_);
lean_dec_ref(v___x_2390_);
lean_dec(v___y_2348_);
lean_dec(v___y_2350_);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v___x_2391_, 0);
lean_dec(v_unused_2399_);
v___x_2393_ = v___x_2391_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_dec(v___x_2391_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v_a_2385_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2385_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_a_2402_ = lean_ctor_get(v_r_2384_, 0);
lean_inc(v_a_2402_);
lean_dec_ref(v_r_2384_);
v___x_2403_ = lean_box(0);
v___x_2404_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2350_, v_isExporting_2354_, v___x_2368_, v___y_2348_, v___x_2380_, v___x_2403_);
lean_dec(v___y_2348_);
lean_dec(v___y_2350_);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v___x_2404_, 0);
lean_dec(v_unused_2412_);
v___x_2406_ = v___x_2404_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_dec(v___x_2404_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set_tag(v___x_2406_, 1);
lean_ctor_set(v___x_2406_, 0, v_a_2402_);
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2402_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2419_, lean_object* v_isExporting_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v_isExporting_boxed_2426_; lean_object* v_res_2427_; 
v_isExporting_boxed_2426_ = lean_unbox(v_isExporting_2420_);
v_res_2427_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2419_, v_isExporting_boxed_2426_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2428_, uint8_t v_when_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
if (v_when_2429_ == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_apply_5(v_x_2428_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, lean_box(0));
return v___x_2435_;
}
else
{
uint8_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = 0;
v___x_2437_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2428_, v___x_2436_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2438_, lean_object* v_when_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v_when_boxed_2445_; lean_object* v_res_2446_; 
v_when_boxed_2445_ = lean_unbox(v_when_2439_);
v_res_2446_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2438_, v_when_boxed_2445_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
return v_res_2446_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2456_, uint8_t v_nonRec_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; lean_object* v_env_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___f_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2463_ = lean_st_ref_get(v___y_2461_);
v_env_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_ref(v_env_2464_);
lean_dec(v___x_2463_);
v___x_2465_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2456_);
v___x_2466_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2464_, v_declName_2456_, v___x_2465_);
v___x_2467_ = lean_box(v_nonRec_2457_);
lean_inc(v___x_2466_);
v___f_2468_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2468_, 0, v___x_2466_);
lean_closure_set(v___f_2468_, 1, v_declName_2456_);
lean_closure_set(v___f_2468_, 2, v___x_2467_);
lean_closure_set(v___f_2468_, 3, v___x_2465_);
v___x_2469_ = 1;
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
v___x_2470_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2468_, v___x_2469_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
if (lean_obj_tag(v_a_2471_) == 1)
{
lean_object* v_val_2472_; uint8_t v___x_2473_; 
v_val_2472_ = lean_ctor_get(v_a_2471_, 0);
lean_inc(v_val_2472_);
lean_dec_ref(v_a_2471_);
v___x_2473_ = lean_name_eq(v_val_2472_, v___x_2466_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v___x_2470_);
v___x_2474_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2475_ = l_Lean_MessageData_ofName(v_val_2472_);
v___x_2476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = l_Lean_MessageData_ofName(v___x_2466_);
v___x_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2482_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
else
{
lean_dec(v_val_2472_);
lean_dec(v___x_2466_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v___x_2470_;
}
}
else
{
lean_dec(v_a_2471_);
lean_dec(v___x_2466_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v___x_2470_;
}
}
else
{
lean_dec(v___x_2466_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v___x_2470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2492_, lean_object* v_nonRec_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v_nonRec_boxed_2499_; lean_object* v_res_2500_; 
v_nonRec_boxed_2499_ = lean_unbox(v_nonRec_2493_);
v_res_2500_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2492_, v_nonRec_boxed_2499_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2501_, uint8_t v_nonRec_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2508_; lean_object* v___f_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2508_ = lean_box(v_nonRec_2502_);
v___f_2509_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2509_, 0, v_declName_2501_);
lean_closure_set(v___f_2509_, 1, v___x_2508_);
v___x_2510_ = lean_unsigned_to_nat(32u);
v___x_2511_ = lean_mk_empty_array_with_capacity(v___x_2510_);
lean_dec_ref(v___x_2511_);
v___x_2512_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2513_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2514_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2512_, v___x_2513_, v___f_2509_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2515_, lean_object* v_nonRec_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
uint8_t v_nonRec_boxed_2522_; lean_object* v_res_2523_; 
v_nonRec_boxed_2522_ = lean_unbox(v_nonRec_2516_);
v_res_2523_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2515_, v_nonRec_boxed_2522_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2524_, lean_object* v_as_2525_, lean_object* v_as_x27_2526_, lean_object* v_b_2527_, lean_object* v_a_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2524_, v_as_x27_2526_, v_b_2527_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2535_, lean_object* v_as_2536_, lean_object* v_as_x27_2537_, lean_object* v_b_2538_, lean_object* v_a_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2535_, v_as_2536_, v_as_x27_2537_, v_b_2538_, v_a_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v_as_2536_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2546_, lean_object* v_x_2547_, uint8_t v_isExporting_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2547_, v_isExporting_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2555_, lean_object* v_x_2556_, lean_object* v_isExporting_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
uint8_t v_isExporting_boxed_2563_; lean_object* v_res_2564_; 
v_isExporting_boxed_2563_ = lean_unbox(v_isExporting_2557_);
v_res_2564_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2555_, v_x_2556_, v_isExporting_boxed_2563_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2565_, lean_object* v_x_2566_, uint8_t v_when_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2566_, v_when_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2574_, lean_object* v_x_2575_, lean_object* v_when_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
uint8_t v_when_boxed_2582_; lean_object* v_res_2583_; 
v_when_boxed_2582_ = lean_unbox(v_when_2576_);
v_res_2583_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2574_, v_x_2575_, v_when_boxed_2582_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2584_, lean_object* v_msg_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2592_, lean_object* v_msg_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2592_, v_msg_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v_cls_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_options_2603_; uint8_t v_hasTrace_2604_; 
v_options_2603_ = lean_ctor_get(v___y_2601_, 2);
v_hasTrace_2604_ = lean_ctor_get_uint8(v_options_2603_, sizeof(void*)*1);
if (v_hasTrace_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec(v_cls_2600_);
v___x_2605_ = lean_box(v_hasTrace_2604_);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
else
{
lean_object* v_inheritedTraceOptions_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_inheritedTraceOptions_2607_ = lean_ctor_get(v___y_2601_, 13);
v___x_2608_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_2609_ = l_Lean_Name_append(v___x_2608_, v_cls_2600_);
v___x_2610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2607_, v_options_2603_, v___x_2609_);
lean_dec(v___x_2609_);
v___x_2611_ = lean_box(v___x_2610_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_cls_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v_cls_2613_, v___y_2614_);
lean_dec_ref(v___y_2614_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v_cls_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v_cls_2617_, v___y_2618_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v_cls_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v_cls_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2626_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_unsigned_to_nat(32u);
v___x_2628_ = lean_mk_empty_array_with_capacity(v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
return v___x_2629_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2630_ = ((size_t)5ULL);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = lean_unsigned_to_nat(32u);
v___x_2633_ = lean_mk_empty_array_with_capacity(v___x_2632_);
v___x_2634_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_2635_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v___x_2633_);
lean_ctor_set(v___x_2635_, 2, v___x_2631_);
lean_ctor_set(v___x_2635_, 3, v___x_2631_);
lean_ctor_set_usize(v___x_2635_, 4, v___x_2630_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; lean_object* v_traceState_2639_; lean_object* v_traces_2640_; lean_object* v___x_2641_; lean_object* v_traceState_2642_; lean_object* v_env_2643_; lean_object* v_nextMacroScope_2644_; lean_object* v_ngen_2645_; lean_object* v_auxDeclNGen_2646_; lean_object* v_cache_2647_; lean_object* v_messages_2648_; lean_object* v_infoState_2649_; lean_object* v_snapshotTasks_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2669_; 
v___x_2638_ = lean_st_ref_get(v___y_2636_);
v_traceState_2639_ = lean_ctor_get(v___x_2638_, 4);
lean_inc_ref(v_traceState_2639_);
lean_dec(v___x_2638_);
v_traces_2640_ = lean_ctor_get(v_traceState_2639_, 0);
lean_inc_ref(v_traces_2640_);
lean_dec_ref(v_traceState_2639_);
v___x_2641_ = lean_st_ref_take(v___y_2636_);
v_traceState_2642_ = lean_ctor_get(v___x_2641_, 4);
v_env_2643_ = lean_ctor_get(v___x_2641_, 0);
v_nextMacroScope_2644_ = lean_ctor_get(v___x_2641_, 1);
v_ngen_2645_ = lean_ctor_get(v___x_2641_, 2);
v_auxDeclNGen_2646_ = lean_ctor_get(v___x_2641_, 3);
v_cache_2647_ = lean_ctor_get(v___x_2641_, 5);
v_messages_2648_ = lean_ctor_get(v___x_2641_, 6);
v_infoState_2649_ = lean_ctor_get(v___x_2641_, 7);
v_snapshotTasks_2650_ = lean_ctor_get(v___x_2641_, 8);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2652_ = v___x_2641_;
v_isShared_2653_ = v_isSharedCheck_2669_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_snapshotTasks_2650_);
lean_inc(v_infoState_2649_);
lean_inc(v_messages_2648_);
lean_inc(v_cache_2647_);
lean_inc(v_traceState_2642_);
lean_inc(v_auxDeclNGen_2646_);
lean_inc(v_ngen_2645_);
lean_inc(v_nextMacroScope_2644_);
lean_inc(v_env_2643_);
lean_dec(v___x_2641_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2669_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
uint64_t v_tid_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2667_; 
v_tid_2654_ = lean_ctor_get_uint64(v_traceState_2642_, sizeof(void*)*1);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_traceState_2642_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v_traceState_2642_, 0);
lean_dec(v_unused_2668_);
v___x_2656_ = v_traceState_2642_;
v_isShared_2657_ = v_isSharedCheck_2667_;
goto v_resetjp_2655_;
}
else
{
lean_dec(v_traceState_2642_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2667_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___closed__1);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2658_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2658_);
lean_ctor_set_uint64(v_reuseFailAlloc_2666_, sizeof(void*)*1, v_tid_2654_);
v___x_2660_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2662_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 4, v___x_2660_);
v___x_2662_ = v___x_2652_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_env_2643_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_nextMacroScope_2644_);
lean_ctor_set(v_reuseFailAlloc_2665_, 2, v_ngen_2645_);
lean_ctor_set(v_reuseFailAlloc_2665_, 3, v_auxDeclNGen_2646_);
lean_ctor_set(v_reuseFailAlloc_2665_, 4, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2665_, 5, v_cache_2647_);
lean_ctor_set(v_reuseFailAlloc_2665_, 6, v_messages_2648_);
lean_ctor_set(v_reuseFailAlloc_2665_, 7, v_infoState_2649_);
lean_ctor_set(v_reuseFailAlloc_2665_, 8, v_snapshotTasks_2650_);
v___x_2662_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_st_ref_set(v___y_2636_, v___x_2662_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_traces_2640_);
return v___x_2664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_2670_);
lean_dec(v___y_2670_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = 0;
v___x_2686_ = lean_box(v___x_2685_);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
return v_res_2692_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2695_ = l_Lean_stringToMessageData(v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2696_, lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2701_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2702_ = l_Lean_MessageData_ofName(v_name_2696_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2705_, lean_object* v_x_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2705_, v_x_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec_ref(v_x_2706_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(lean_object* v_x_2711_){
_start:
{
if (lean_obj_tag(v_x_2711_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v_x_2711_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_x_2711_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v_x_2711_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v_x_2711_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set_tag(v___x_2715_, 1);
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
v_a_2721_ = lean_ctor_get(v_x_2711_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_x_2711_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v_x_2711_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v_x_2711_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 0);
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg___boxed(lean_object* v_x_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_x_2729_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(size_t v_sz_2732_, size_t v_i_2733_, lean_object* v_bs_2734_){
_start:
{
uint8_t v___x_2735_; 
v___x_2735_ = lean_usize_dec_lt(v_i_2733_, v_sz_2732_);
if (v___x_2735_ == 0)
{
return v_bs_2734_;
}
else
{
lean_object* v_v_2736_; lean_object* v_msg_2737_; lean_object* v___x_2738_; lean_object* v_bs_x27_2739_; size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v_v_2736_ = lean_array_uget_borrowed(v_bs_2734_, v_i_2733_);
v_msg_2737_ = lean_ctor_get(v_v_2736_, 1);
lean_inc_ref(v_msg_2737_);
v___x_2738_ = lean_unsigned_to_nat(0u);
v_bs_x27_2739_ = lean_array_uset(v_bs_2734_, v_i_2733_, v___x_2738_);
v___x_2740_ = ((size_t)1ULL);
v___x_2741_ = lean_usize_add(v_i_2733_, v___x_2740_);
v___x_2742_ = lean_array_uset(v_bs_x27_2739_, v_i_2733_, v_msg_2737_);
v_i_2733_ = v___x_2741_;
v_bs_2734_ = v___x_2742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_sz_2744_, lean_object* v_i_2745_, lean_object* v_bs_2746_){
_start:
{
size_t v_sz_boxed_2747_; size_t v_i_boxed_2748_; lean_object* v_res_2749_; 
v_sz_boxed_2747_ = lean_unbox_usize(v_sz_2744_);
lean_dec(v_sz_2744_);
v_i_boxed_2748_ = lean_unbox_usize(v_i_2745_);
lean_dec(v_i_2745_);
v_res_2749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_sz_boxed_2747_, v_i_boxed_2748_, v_bs_2746_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_oldTraces_2750_, lean_object* v_data_2751_, lean_object* v_ref_2752_, lean_object* v_msg_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_fileName_2757_; lean_object* v_fileMap_2758_; lean_object* v_options_2759_; lean_object* v_currRecDepth_2760_; lean_object* v_maxRecDepth_2761_; lean_object* v_ref_2762_; lean_object* v_currNamespace_2763_; lean_object* v_openDecls_2764_; lean_object* v_initHeartbeats_2765_; lean_object* v_maxHeartbeats_2766_; lean_object* v_quotContext_2767_; lean_object* v_currMacroScope_2768_; uint8_t v_diag_2769_; lean_object* v_cancelTk_x3f_2770_; uint8_t v_suppressElabErrors_2771_; lean_object* v_inheritedTraceOptions_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2827_; 
v_fileName_2757_ = lean_ctor_get(v___y_2754_, 0);
v_fileMap_2758_ = lean_ctor_get(v___y_2754_, 1);
v_options_2759_ = lean_ctor_get(v___y_2754_, 2);
v_currRecDepth_2760_ = lean_ctor_get(v___y_2754_, 3);
v_maxRecDepth_2761_ = lean_ctor_get(v___y_2754_, 4);
v_ref_2762_ = lean_ctor_get(v___y_2754_, 5);
v_currNamespace_2763_ = lean_ctor_get(v___y_2754_, 6);
v_openDecls_2764_ = lean_ctor_get(v___y_2754_, 7);
v_initHeartbeats_2765_ = lean_ctor_get(v___y_2754_, 8);
v_maxHeartbeats_2766_ = lean_ctor_get(v___y_2754_, 9);
v_quotContext_2767_ = lean_ctor_get(v___y_2754_, 10);
v_currMacroScope_2768_ = lean_ctor_get(v___y_2754_, 11);
v_diag_2769_ = lean_ctor_get_uint8(v___y_2754_, sizeof(void*)*14);
v_cancelTk_x3f_2770_ = lean_ctor_get(v___y_2754_, 12);
v_suppressElabErrors_2771_ = lean_ctor_get_uint8(v___y_2754_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2772_ = lean_ctor_get(v___y_2754_, 13);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___y_2754_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2774_ = v___y_2754_;
v_isShared_2775_ = v_isSharedCheck_2827_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_inheritedTraceOptions_2772_);
lean_inc(v_cancelTk_x3f_2770_);
lean_inc(v_currMacroScope_2768_);
lean_inc(v_quotContext_2767_);
lean_inc(v_maxHeartbeats_2766_);
lean_inc(v_initHeartbeats_2765_);
lean_inc(v_openDecls_2764_);
lean_inc(v_currNamespace_2763_);
lean_inc(v_ref_2762_);
lean_inc(v_maxRecDepth_2761_);
lean_inc(v_currRecDepth_2760_);
lean_inc(v_options_2759_);
lean_inc(v_fileMap_2758_);
lean_inc(v_fileName_2757_);
lean_dec(v___y_2754_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2827_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v_traceState_2777_; lean_object* v_traces_2778_; lean_object* v_ref_2779_; lean_object* v___x_2781_; 
v___x_2776_ = lean_st_ref_get(v___y_2755_);
v_traceState_2777_ = lean_ctor_get(v___x_2776_, 4);
lean_inc_ref(v_traceState_2777_);
lean_dec(v___x_2776_);
v_traces_2778_ = lean_ctor_get(v_traceState_2777_, 0);
lean_inc_ref(v_traces_2778_);
lean_dec_ref(v_traceState_2777_);
v_ref_2779_ = l_Lean_replaceRef(v_ref_2752_, v_ref_2762_);
lean_dec(v_ref_2762_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 5, v_ref_2779_);
v___x_2781_ = v___x_2774_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_fileName_2757_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_fileMap_2758_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_options_2759_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_currRecDepth_2760_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_maxRecDepth_2761_);
lean_ctor_set(v_reuseFailAlloc_2826_, 5, v_ref_2779_);
lean_ctor_set(v_reuseFailAlloc_2826_, 6, v_currNamespace_2763_);
lean_ctor_set(v_reuseFailAlloc_2826_, 7, v_openDecls_2764_);
lean_ctor_set(v_reuseFailAlloc_2826_, 8, v_initHeartbeats_2765_);
lean_ctor_set(v_reuseFailAlloc_2826_, 9, v_maxHeartbeats_2766_);
lean_ctor_set(v_reuseFailAlloc_2826_, 10, v_quotContext_2767_);
lean_ctor_set(v_reuseFailAlloc_2826_, 11, v_currMacroScope_2768_);
lean_ctor_set(v_reuseFailAlloc_2826_, 12, v_cancelTk_x3f_2770_);
lean_ctor_set(v_reuseFailAlloc_2826_, 13, v_inheritedTraceOptions_2772_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, sizeof(void*)*14, v_diag_2769_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, sizeof(void*)*14 + 1, v_suppressElabErrors_2771_);
v___x_2781_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; size_t v_sz_2783_; size_t v___x_2784_; lean_object* v___x_2785_; lean_object* v_msg_2786_; lean_object* v___x_2787_; lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2825_; 
v___x_2782_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2778_);
lean_dec_ref(v_traces_2778_);
v_sz_2783_ = lean_array_size(v___x_2782_);
v___x_2784_ = ((size_t)0ULL);
v___x_2785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_sz_2783_, v___x_2784_, v___x_2782_);
v_msg_2786_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2786_, 0, v_data_2751_);
lean_ctor_set(v_msg_2786_, 1, v_msg_2753_);
lean_ctor_set(v_msg_2786_, 2, v___x_2785_);
v___x_2787_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2786_, v___x_2781_, v___y_2755_);
lean_dec_ref(v___x_2781_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2825_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2825_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2792_; lean_object* v_traceState_2793_; lean_object* v_env_2794_; lean_object* v_nextMacroScope_2795_; lean_object* v_ngen_2796_; lean_object* v_auxDeclNGen_2797_; lean_object* v_cache_2798_; lean_object* v_messages_2799_; lean_object* v_infoState_2800_; lean_object* v_snapshotTasks_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2824_; 
v___x_2792_ = lean_st_ref_take(v___y_2755_);
v_traceState_2793_ = lean_ctor_get(v___x_2792_, 4);
v_env_2794_ = lean_ctor_get(v___x_2792_, 0);
v_nextMacroScope_2795_ = lean_ctor_get(v___x_2792_, 1);
v_ngen_2796_ = lean_ctor_get(v___x_2792_, 2);
v_auxDeclNGen_2797_ = lean_ctor_get(v___x_2792_, 3);
v_cache_2798_ = lean_ctor_get(v___x_2792_, 5);
v_messages_2799_ = lean_ctor_get(v___x_2792_, 6);
v_infoState_2800_ = lean_ctor_get(v___x_2792_, 7);
v_snapshotTasks_2801_ = lean_ctor_get(v___x_2792_, 8);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2803_ = v___x_2792_;
v_isShared_2804_ = v_isSharedCheck_2824_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_snapshotTasks_2801_);
lean_inc(v_infoState_2800_);
lean_inc(v_messages_2799_);
lean_inc(v_cache_2798_);
lean_inc(v_traceState_2793_);
lean_inc(v_auxDeclNGen_2797_);
lean_inc(v_ngen_2796_);
lean_inc(v_nextMacroScope_2795_);
lean_inc(v_env_2794_);
lean_dec(v___x_2792_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2824_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
uint64_t v_tid_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2822_; 
v_tid_2805_ = lean_ctor_get_uint64(v_traceState_2793_, sizeof(void*)*1);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_traceState_2793_);
if (v_isSharedCheck_2822_ == 0)
{
lean_object* v_unused_2823_; 
v_unused_2823_ = lean_ctor_get(v_traceState_2793_, 0);
lean_dec(v_unused_2823_);
v___x_2807_ = v_traceState_2793_;
v_isShared_2808_ = v_isSharedCheck_2822_;
goto v_resetjp_2806_;
}
else
{
lean_dec(v_traceState_2793_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2822_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v_ref_2752_);
lean_ctor_set(v___x_2809_, 1, v_a_2788_);
v___x_2810_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2750_, v___x_2809_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2810_);
lean_ctor_set_uint64(v_reuseFailAlloc_2821_, sizeof(void*)*1, v_tid_2805_);
v___x_2812_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2814_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 4, v___x_2812_);
v___x_2814_ = v___x_2803_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_env_2794_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_nextMacroScope_2795_);
lean_ctor_set(v_reuseFailAlloc_2820_, 2, v_ngen_2796_);
lean_ctor_set(v_reuseFailAlloc_2820_, 3, v_auxDeclNGen_2797_);
lean_ctor_set(v_reuseFailAlloc_2820_, 4, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2820_, 5, v_cache_2798_);
lean_ctor_set(v_reuseFailAlloc_2820_, 6, v_messages_2799_);
lean_ctor_set(v_reuseFailAlloc_2820_, 7, v_infoState_2800_);
lean_ctor_set(v_reuseFailAlloc_2820_, 8, v_snapshotTasks_2801_);
v___x_2814_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2815_ = lean_st_ref_set(v___y_2755_, v___x_2814_);
v___x_2816_ = lean_box(0);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2816_);
v___x_2818_ = v___x_2790_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_oldTraces_2828_, lean_object* v_data_2829_, lean_object* v_ref_2830_, lean_object* v_msg_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(v_oldTraces_2828_, v_data_2829_, v_ref_2830_, v_msg_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
return v_res_2835_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(lean_object* v_e_2836_){
_start:
{
if (lean_obj_tag(v_e_2836_) == 0)
{
uint8_t v___x_2837_; 
v___x_2837_ = 2;
return v___x_2837_;
}
else
{
lean_object* v_a_2838_; uint8_t v___x_2839_; 
v_a_2838_ = lean_ctor_get(v_e_2836_, 0);
v___x_2839_ = lean_unbox(v_a_2838_);
if (v___x_2839_ == 0)
{
uint8_t v___x_2840_; 
v___x_2840_ = 1;
return v___x_2840_;
}
else
{
uint8_t v___x_2841_; 
v___x_2841_ = 0;
return v___x_2841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2___boxed(lean_object* v_e_2842_){
_start:
{
uint8_t v_res_2843_; lean_object* v_r_2844_; 
v_res_2843_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(v_e_2842_);
lean_dec_ref(v_e_2842_);
v_r_2844_ = lean_box(v_res_2843_);
return v_r_2844_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__0));
v___x_2847_ = l_Lean_stringToMessageData(v___x_2846_);
return v___x_2847_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__2));
v___x_2850_ = l_Lean_stringToMessageData(v___x_2849_);
return v___x_2850_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4(void){
_start:
{
lean_object* v___x_2851_; double v___x_2852_; 
v___x_2851_ = lean_unsigned_to_nat(1000u);
v___x_2852_ = lean_float_of_nat(v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(lean_object* v_cls_2853_, uint8_t v_collapsed_2854_, lean_object* v_tag_2855_, lean_object* v_opts_2856_, uint8_t v_clsEnabled_2857_, lean_object* v_oldTraces_2858_, lean_object* v_msg_2859_, lean_object* v_resStartStop_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_fst_2864_; lean_object* v_snd_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2963_; 
v_fst_2864_ = lean_ctor_get(v_resStartStop_2860_, 0);
v_snd_2865_ = lean_ctor_get(v_resStartStop_2860_, 1);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_resStartStop_2860_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2867_ = v_resStartStop_2860_;
v_isShared_2868_ = v_isSharedCheck_2963_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_snd_2865_);
lean_inc(v_fst_2864_);
lean_dec(v_resStartStop_2860_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2963_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v_data_2872_; lean_object* v_fst_2883_; lean_object* v_snd_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2962_; 
v_fst_2883_ = lean_ctor_get(v_snd_2865_, 0);
v_snd_2884_ = lean_ctor_get(v_snd_2865_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_snd_2865_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2886_ = v_snd_2865_;
v_isShared_2887_ = v_isSharedCheck_2962_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_snd_2884_);
lean_inc(v_fst_2883_);
lean_dec(v_snd_2865_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2962_;
goto v_resetjp_2885_;
}
v___jp_2869_:
{
lean_object* v___x_2873_; 
v___x_2873_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__3(v_oldTraces_2858_, v_data_2872_, v___y_2871_, v___y_2870_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v___x_2874_; 
lean_dec_ref(v___x_2873_);
v___x_2874_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_fst_2864_);
return v___x_2874_;
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_fst_2864_);
v_a_2875_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2873_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2873_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; uint8_t v___x_2889_; lean_object* v___y_2891_; lean_object* v_a_2892_; uint8_t v___y_2916_; double v___y_2947_; 
v___x_2888_ = l_Lean_trace_profiler;
v___x_2889_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2856_, v___x_2888_);
if (v___x_2889_ == 0)
{
v___y_2916_ = v___x_2889_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2953_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2856_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; double v___x_2956_; double v___x_2957_; double v___x_2958_; 
v___x_2954_ = l_Lean_trace_profiler_threshold;
v___x_2955_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2856_, v___x_2954_);
v___x_2956_ = lean_float_of_nat(v___x_2955_);
v___x_2957_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__4);
v___x_2958_ = lean_float_div(v___x_2956_, v___x_2957_);
v___y_2947_ = v___x_2958_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; double v___x_2961_; 
v___x_2959_ = l_Lean_trace_profiler_threshold;
v___x_2960_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2856_, v___x_2959_);
v___x_2961_ = lean_float_of_nat(v___x_2960_);
v___y_2947_ = v___x_2961_;
goto v___jp_2946_;
}
}
v___jp_2890_:
{
uint8_t v_result_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v_result_2893_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__2(v_fst_2864_);
v___x_2894_ = l_Lean_TraceResult_toEmoji(v_result_2893_);
v___x_2895_ = l_Lean_stringToMessageData(v___x_2894_);
v___x_2896_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__1);
if (v_isShared_2887_ == 0)
{
lean_ctor_set_tag(v___x_2886_, 7);
lean_ctor_set(v___x_2886_, 1, v___x_2896_);
lean_ctor_set(v___x_2886_, 0, v___x_2895_);
v___x_2898_ = v___x_2886_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v_m_2900_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set_tag(v___x_2867_, 7);
lean_ctor_set(v___x_2867_, 1, v_a_2892_);
lean_ctor_set(v___x_2867_, 0, v___x_2898_);
v_m_2900_ = v___x_2867_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_a_2892_);
v_m_2900_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; double v___x_2903_; lean_object* v_data_2904_; 
v___x_2901_ = lean_box(v_result_2893_);
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
v___x_2903_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__0);
lean_inc_ref(v_tag_2855_);
lean_inc_ref(v___x_2902_);
lean_inc(v_cls_2853_);
v_data_2904_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2904_, 0, v_cls_2853_);
lean_ctor_set(v_data_2904_, 1, v___x_2902_);
lean_ctor_set(v_data_2904_, 2, v_tag_2855_);
lean_ctor_set_float(v_data_2904_, sizeof(void*)*3, v___x_2903_);
lean_ctor_set_float(v_data_2904_, sizeof(void*)*3 + 8, v___x_2903_);
lean_ctor_set_uint8(v_data_2904_, sizeof(void*)*3 + 16, v_collapsed_2854_);
if (v___x_2889_ == 0)
{
lean_dec_ref(v___x_2902_);
lean_dec(v_snd_2884_);
lean_dec(v_fst_2883_);
lean_dec_ref(v_tag_2855_);
lean_dec(v_cls_2853_);
v___y_2870_ = v_m_2900_;
v___y_2871_ = v___y_2891_;
v_data_2872_ = v_data_2904_;
goto v___jp_2869_;
}
else
{
lean_object* v_data_2905_; double v___x_2906_; double v___x_2907_; 
lean_dec_ref(v_data_2904_);
v_data_2905_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2905_, 0, v_cls_2853_);
lean_ctor_set(v_data_2905_, 1, v___x_2902_);
lean_ctor_set(v_data_2905_, 2, v_tag_2855_);
v___x_2906_ = lean_unbox_float(v_fst_2883_);
lean_dec(v_fst_2883_);
lean_ctor_set_float(v_data_2905_, sizeof(void*)*3, v___x_2906_);
v___x_2907_ = lean_unbox_float(v_snd_2884_);
lean_dec(v_snd_2884_);
lean_ctor_set_float(v_data_2905_, sizeof(void*)*3 + 8, v___x_2907_);
lean_ctor_set_uint8(v_data_2905_, sizeof(void*)*3 + 16, v_collapsed_2854_);
v___y_2870_ = v_m_2900_;
v___y_2871_ = v___y_2891_;
v_data_2872_ = v_data_2905_;
goto v___jp_2869_;
}
}
}
}
v___jp_2910_:
{
lean_object* v_ref_2911_; lean_object* v___x_2912_; 
v_ref_2911_ = lean_ctor_get(v___y_2861_, 5);
lean_inc(v___y_2862_);
lean_inc_ref(v___y_2861_);
lean_inc(v_fst_2864_);
v___x_2912_ = lean_apply_4(v_msg_2859_, v_fst_2864_, v___y_2861_, v___y_2862_, lean_box(0));
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
lean_inc(v_ref_2911_);
v___y_2891_ = v_ref_2911_;
v_a_2892_ = v_a_2913_;
goto v___jp_2890_;
}
else
{
lean_object* v___x_2914_; 
lean_dec_ref(v___x_2912_);
v___x_2914_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___closed__3);
lean_inc(v_ref_2911_);
v___y_2891_ = v_ref_2911_;
v_a_2892_ = v___x_2914_;
goto v___jp_2890_;
}
}
v___jp_2915_:
{
if (v_clsEnabled_2857_ == 0)
{
if (v___y_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v_traceState_2918_; lean_object* v_env_2919_; lean_object* v_nextMacroScope_2920_; lean_object* v_ngen_2921_; lean_object* v_auxDeclNGen_2922_; lean_object* v_cache_2923_; lean_object* v_messages_2924_; lean_object* v_infoState_2925_; lean_object* v_snapshotTasks_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2945_; 
lean_del_object(v___x_2886_);
lean_dec(v_snd_2884_);
lean_dec(v_fst_2883_);
lean_del_object(v___x_2867_);
lean_dec_ref(v___y_2861_);
lean_dec_ref(v_msg_2859_);
lean_dec_ref(v_tag_2855_);
lean_dec(v_cls_2853_);
v___x_2917_ = lean_st_ref_take(v___y_2862_);
v_traceState_2918_ = lean_ctor_get(v___x_2917_, 4);
v_env_2919_ = lean_ctor_get(v___x_2917_, 0);
v_nextMacroScope_2920_ = lean_ctor_get(v___x_2917_, 1);
v_ngen_2921_ = lean_ctor_get(v___x_2917_, 2);
v_auxDeclNGen_2922_ = lean_ctor_get(v___x_2917_, 3);
v_cache_2923_ = lean_ctor_get(v___x_2917_, 5);
v_messages_2924_ = lean_ctor_get(v___x_2917_, 6);
v_infoState_2925_ = lean_ctor_get(v___x_2917_, 7);
v_snapshotTasks_2926_ = lean_ctor_get(v___x_2917_, 8);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2928_ = v___x_2917_;
v_isShared_2929_ = v_isSharedCheck_2945_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_snapshotTasks_2926_);
lean_inc(v_infoState_2925_);
lean_inc(v_messages_2924_);
lean_inc(v_cache_2923_);
lean_inc(v_traceState_2918_);
lean_inc(v_auxDeclNGen_2922_);
lean_inc(v_ngen_2921_);
lean_inc(v_nextMacroScope_2920_);
lean_inc(v_env_2919_);
lean_dec(v___x_2917_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2945_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
uint64_t v_tid_2930_; lean_object* v_traces_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2944_; 
v_tid_2930_ = lean_ctor_get_uint64(v_traceState_2918_, sizeof(void*)*1);
v_traces_2931_ = lean_ctor_get(v_traceState_2918_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_traceState_2918_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2933_ = v_traceState_2918_;
v_isShared_2934_ = v_isSharedCheck_2944_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_traces_2931_);
lean_dec(v_traceState_2918_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2944_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2935_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2858_, v_traces_2931_);
lean_dec_ref(v_traces_2931_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2935_);
v___x_2937_ = v___x_2933_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2935_);
lean_ctor_set_uint64(v_reuseFailAlloc_2943_, sizeof(void*)*1, v_tid_2930_);
v___x_2937_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2939_; 
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 4, v___x_2937_);
v___x_2939_ = v___x_2928_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_env_2919_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_nextMacroScope_2920_);
lean_ctor_set(v_reuseFailAlloc_2942_, 2, v_ngen_2921_);
lean_ctor_set(v_reuseFailAlloc_2942_, 3, v_auxDeclNGen_2922_);
lean_ctor_set(v_reuseFailAlloc_2942_, 4, v___x_2937_);
lean_ctor_set(v_reuseFailAlloc_2942_, 5, v_cache_2923_);
lean_ctor_set(v_reuseFailAlloc_2942_, 6, v_messages_2924_);
lean_ctor_set(v_reuseFailAlloc_2942_, 7, v_infoState_2925_);
lean_ctor_set(v_reuseFailAlloc_2942_, 8, v_snapshotTasks_2926_);
v___x_2939_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_st_ref_set(v___y_2862_, v___x_2939_);
lean_dec(v___y_2862_);
v___x_2941_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_fst_2864_);
return v___x_2941_;
}
}
}
}
}
else
{
goto v___jp_2910_;
}
}
else
{
goto v___jp_2910_;
}
}
v___jp_2946_:
{
double v___x_2948_; double v___x_2949_; double v___x_2950_; uint8_t v___x_2951_; 
v___x_2948_ = lean_unbox_float(v_snd_2884_);
v___x_2949_ = lean_unbox_float(v_fst_2883_);
v___x_2950_ = lean_float_sub(v___x_2948_, v___x_2949_);
v___x_2951_ = lean_float_decLt(v___y_2947_, v___x_2950_);
v___y_2916_ = v___x_2951_;
goto v___jp_2915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_2964_, lean_object* v_collapsed_2965_, lean_object* v_tag_2966_, lean_object* v_opts_2967_, lean_object* v_clsEnabled_2968_, lean_object* v_oldTraces_2969_, lean_object* v_msg_2970_, lean_object* v_resStartStop_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
uint8_t v_collapsed_boxed_2975_; uint8_t v_clsEnabled_boxed_2976_; lean_object* v_res_2977_; 
v_collapsed_boxed_2975_ = lean_unbox(v_collapsed_2965_);
v_clsEnabled_boxed_2976_ = lean_unbox(v_clsEnabled_2968_);
v_res_2977_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v_cls_2964_, v_collapsed_boxed_2975_, v_tag_2966_, v_opts_2967_, v_clsEnabled_boxed_2976_, v_oldTraces_2969_, v_msg_2970_, v_resStartStop_2971_, v___y_2972_, v___y_2973_);
lean_dec_ref(v_opts_2967_);
return v_res_2977_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2978_ = lean_box(1);
v___x_2979_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_2980_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set(v___x_2981_, 1, v___x_2979_);
lean_ctor_set(v___x_2981_, 2, v___x_2978_);
return v___x_2981_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2985_ = lean_unsigned_to_nat(0u);
v___x_2986_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
lean_ctor_set(v___x_2986_, 2, v___x_2985_);
lean_ctor_set(v___x_2986_, 3, v___x_2984_);
lean_ctor_set(v___x_2986_, 4, v___x_2984_);
lean_ctor_set(v___x_2986_, 5, v___x_2984_);
lean_ctor_set(v___x_2986_, 6, v___x_2984_);
lean_ctor_set(v___x_2986_, 7, v___x_2984_);
lean_ctor_set(v___x_2986_, 8, v___x_2984_);
return v___x_2986_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2988_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
lean_ctor_set(v___x_2988_, 2, v___x_2987_);
lean_ctor_set(v___x_2988_, 3, v___x_2987_);
lean_ctor_set(v___x_2988_, 4, v___x_2987_);
lean_ctor_set(v___x_2988_, 5, v___x_2987_);
return v___x_2988_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
lean_ctor_set(v___x_2990_, 2, v___x_2989_);
lean_ctor_set(v___x_2990_, 3, v___x_2989_);
lean_ctor_set(v___x_2990_, 4, v___x_2989_);
return v___x_2990_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2991_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2992_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_2993_ = lean_box(1);
v___x_2994_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2995_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
lean_ctor_set(v___x_2996_, 1, v___x_2994_);
lean_ctor_set(v___x_2996_, 2, v___x_2993_);
lean_ctor_set(v___x_2996_, 3, v___x_2992_);
lean_ctor_set(v___x_2996_, 4, v___x_2991_);
return v___x_2996_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3000_; double v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(1000000000u);
v___x_3001_ = lean_float_of_nat(v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_3002_, lean_object* v_name_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_options_3007_; uint8_t v_hasTrace_3008_; 
v_options_3007_ = lean_ctor_get(v___y_3004_, 2);
v_hasTrace_3008_ = lean_ctor_get_uint8(v_options_3007_, sizeof(void*)*1);
if (v_hasTrace_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v_env_3010_; lean_object* v___x_3011_; 
lean_dec_ref(v___f_3002_);
v___x_3009_ = lean_st_ref_get(v___y_3005_);
v_env_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc_ref(v_env_3010_);
lean_dec(v___x_3009_);
lean_inc(v_name_3003_);
v___x_3011_ = l_Lean_Meta_declFromEqLikeName(v_env_3010_, v_name_3003_);
if (lean_obj_tag(v___x_3011_) == 1)
{
lean_object* v_val_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3101_; 
v_val_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3101_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_val_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3101_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v_fst_3016_; lean_object* v_snd_3017_; lean_object* v___x_3018_; lean_object* v_env_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v_fst_3016_ = lean_ctor_get(v_val_3012_, 0);
lean_inc(v_fst_3016_);
v_snd_3017_ = lean_ctor_get(v_val_3012_, 1);
lean_inc(v_snd_3017_);
lean_dec(v_val_3012_);
v___x_3018_ = lean_st_ref_get(v___y_3005_);
v_env_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc_ref(v_env_3019_);
lean_dec(v___x_3018_);
lean_inc(v_snd_3017_);
lean_inc(v_fst_3016_);
v___x_3020_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3019_, v_fst_3016_, v_snd_3017_);
v___x_3021_ = lean_name_eq(v_name_3003_, v___x_3020_);
lean_dec(v___x_3020_);
lean_dec(v_name_3003_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec(v_snd_3017_);
lean_dec(v_fst_3016_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
v___x_3022_ = lean_box(v_hasTrace_3008_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3022_);
v___x_3024_ = v___x_3014_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
else
{
uint8_t v___x_3026_; lean_object* v_a_3028_; 
lean_inc(v_snd_3017_);
v___x_3026_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3017_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3042_; uint8_t v___x_3043_; lean_object* v_a_3045_; 
lean_del_object(v___x_3014_);
v___x_3042_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3043_ = lean_string_dec_eq(v_snd_3017_, v___x_3042_);
lean_dec(v_snd_3017_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec(v_fst_3016_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
v___x_3057_ = lean_box(v_hasTrace_3008_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3059_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3060_ = lean_box(1);
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3062_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3063_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3065_, 0, v___x_3059_);
lean_ctor_set(v___x_3065_, 1, v___x_3060_);
lean_ctor_set(v___x_3065_, 2, v___x_3062_);
lean_ctor_set(v___x_3065_, 3, v___x_3063_);
lean_ctor_set(v___x_3065_, 4, v___x_3064_);
lean_ctor_set(v___x_3065_, 5, v___x_3061_);
lean_ctor_set(v___x_3065_, 6, v___x_3064_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*7, v_hasTrace_3008_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*7 + 1, v_hasTrace_3008_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*7 + 2, v_hasTrace_3008_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*7 + 3, v___x_3021_);
v___x_3066_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3067_ = lean_st_mk_ref(v___x_3066_);
lean_inc(v___x_3067_);
v___x_3068_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3016_, v___x_3021_, v___x_3065_, v___x_3067_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3070_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref(v___x_3068_);
v___x_3070_ = lean_st_ref_get(v___x_3067_);
lean_dec(v___x_3067_);
lean_dec(v___x_3070_);
v_a_3045_ = v_a_3069_;
goto v___jp_3044_;
}
else
{
lean_dec(v___x_3067_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3071_; 
v_a_3071_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3071_);
lean_dec_ref(v___x_3068_);
v_a_3045_ = v_a_3071_;
goto v___jp_3044_;
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
v_a_3072_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3068_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3068_);
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
v___jp_3044_:
{
if (lean_obj_tag(v_a_3045_) == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_box(v_hasTrace_3008_);
v___x_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
return v___x_3047_;
}
else
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3055_; 
v_isSharedCheck_3055_ = !lean_is_exclusive(v_a_3045_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; 
v_unused_3056_ = lean_ctor_get(v_a_3045_, 0);
lean_dec(v_unused_3056_);
v___x_3049_ = v_a_3045_;
v_isShared_3050_ = v_isSharedCheck_3055_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v_a_3045_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3055_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3051_ = lean_box(v___x_3043_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set_tag(v___x_3049_, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3051_);
v___x_3053_ = v___x_3049_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec(v_snd_3017_);
v___x_3080_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3081_ = lean_box(1);
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3084_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3085_ = lean_box(0);
v___x_3086_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3086_, 0, v___x_3080_);
lean_ctor_set(v___x_3086_, 1, v___x_3081_);
lean_ctor_set(v___x_3086_, 2, v___x_3083_);
lean_ctor_set(v___x_3086_, 3, v___x_3084_);
lean_ctor_set(v___x_3086_, 4, v___x_3085_);
lean_ctor_set(v___x_3086_, 5, v___x_3082_);
lean_ctor_set(v___x_3086_, 6, v___x_3085_);
lean_ctor_set_uint8(v___x_3086_, sizeof(void*)*7, v_hasTrace_3008_);
lean_ctor_set_uint8(v___x_3086_, sizeof(void*)*7 + 1, v_hasTrace_3008_);
lean_ctor_set_uint8(v___x_3086_, sizeof(void*)*7 + 2, v_hasTrace_3008_);
lean_ctor_set_uint8(v___x_3086_, sizeof(void*)*7 + 3, v___x_3021_);
v___x_3087_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3088_ = lean_st_mk_ref(v___x_3087_);
lean_inc(v___x_3088_);
v___x_3089_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3016_, v___x_3086_, v___x_3088_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3091_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref(v___x_3089_);
v___x_3091_ = lean_st_ref_get(v___x_3088_);
lean_dec(v___x_3088_);
lean_dec(v___x_3091_);
v_a_3028_ = v_a_3090_;
goto v___jp_3027_;
}
else
{
lean_dec(v___x_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3092_; 
v_a_3092_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3092_);
lean_dec_ref(v___x_3089_);
v_a_3028_ = v_a_3092_;
goto v___jp_3027_;
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_del_object(v___x_3014_);
v_a_3093_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3089_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3089_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
v___jp_3027_:
{
if (lean_obj_tag(v_a_3028_) == 0)
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3029_ = lean_box(v_hasTrace_3008_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3029_);
v___x_3031_ = v___x_3014_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
else
{
lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3040_; 
lean_del_object(v___x_3014_);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_3040_ == 0)
{
lean_object* v_unused_3041_; 
v_unused_3041_ = lean_ctor_get(v_a_3028_, 0);
lean_dec(v_unused_3041_);
v___x_3034_ = v_a_3028_;
v_isShared_3035_ = v_isSharedCheck_3040_;
goto v_resetjp_3033_;
}
else
{
lean_dec(v_a_3028_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3040_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3036_ = lean_box(v___x_3026_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set_tag(v___x_3034_, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3036_);
v___x_3038_ = v___x_3034_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec(v___x_3011_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v_name_3003_);
v___x_3102_ = lean_box(v_hasTrace_3008_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3383_; 
v___x_3104_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3105_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___x_3104_, v___y_3004_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3383_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3383_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___f_3110_; lean_object* v___x_3111_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v_a_3115_; lean_object* v___y_3129_; lean_object* v___y_3130_; uint8_t v_a_3131_; lean_object* v___y_3135_; uint8_t v___y_3136_; lean_object* v___y_3137_; lean_object* v_a_3138_; lean_object* v___y_3140_; uint8_t v___y_3141_; lean_object* v___y_3142_; lean_object* v_a_3143_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v_a_3147_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v_a_3152_; lean_object* v___y_3163_; lean_object* v___y_3164_; uint8_t v_a_3165_; lean_object* v___y_3169_; uint8_t v___y_3170_; uint8_t v___y_3171_; lean_object* v___y_3172_; lean_object* v_a_3173_; lean_object* v___y_3175_; uint8_t v___y_3176_; lean_object* v___y_3177_; lean_object* v_a_3178_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v_a_3183_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v___x_3288_; 
lean_inc(v_name_3003_);
v___f_3110_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3110_, 0, v_name_3003_);
v___x_3111_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__2___closed__1));
v___x_3288_ = lean_unbox(v_a_3106_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; uint8_t v___x_3290_; lean_object* v_a_3292_; lean_object* v_a_3302_; 
v___x_3289_ = l_Lean_trace_profiler;
v___x_3290_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_3007_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3314_; lean_object* v_env_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v___f_3110_);
lean_dec(v_a_3106_);
lean_dec_ref(v___f_3002_);
v___x_3314_ = lean_st_ref_get(v___y_3005_);
v_env_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc_ref(v_env_3315_);
lean_dec(v___x_3314_);
lean_inc(v_name_3003_);
v___x_3316_ = l_Lean_Meta_declFromEqLikeName(v_env_3315_, v_name_3003_);
if (lean_obj_tag(v___x_3316_) == 1)
{
lean_object* v_val_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3380_; 
v_val_3317_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3319_ = v___x_3316_;
v_isShared_3320_ = v_isSharedCheck_3380_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_val_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3380_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3323_; lean_object* v_env_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v_fst_3321_ = lean_ctor_get(v_val_3317_, 0);
lean_inc(v_fst_3321_);
v_snd_3322_ = lean_ctor_get(v_val_3317_, 1);
lean_inc(v_snd_3322_);
lean_dec(v_val_3317_);
v___x_3323_ = lean_st_ref_get(v___y_3005_);
v_env_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc_ref(v_env_3324_);
lean_dec(v___x_3323_);
lean_inc(v_snd_3322_);
lean_inc(v_fst_3321_);
v___x_3325_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3324_, v_fst_3321_, v_snd_3322_);
v___x_3326_ = lean_name_eq(v_name_3003_, v___x_3325_);
lean_dec(v___x_3325_);
lean_dec(v_name_3003_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3329_; 
lean_dec(v_snd_3322_);
lean_dec(v_fst_3321_);
lean_del_object(v___x_3108_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
v___x_3327_ = lean_box(v___x_3290_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set_tag(v___x_3319_, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3327_);
v___x_3329_ = v___x_3319_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
else
{
uint8_t v___x_3331_; 
lean_inc(v_snd_3322_);
v___x_3331_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3322_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; uint8_t v___x_3333_; 
lean_del_object(v___x_3108_);
v___x_3332_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3333_ = lean_string_dec_eq(v_snd_3322_, v___x_3332_);
lean_dec(v_snd_3322_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
lean_dec(v_fst_3321_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
v___x_3334_ = lean_box(v___x_3290_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set_tag(v___x_3319_, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3334_);
v___x_3336_ = v___x_3319_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_del_object(v___x_3319_);
v___x_3338_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3339_ = lean_box(1);
v___x_3340_ = lean_unsigned_to_nat(0u);
v___x_3341_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3344_, 0, v___x_3338_);
lean_ctor_set(v___x_3344_, 1, v___x_3339_);
lean_ctor_set(v___x_3344_, 2, v___x_3341_);
lean_ctor_set(v___x_3344_, 3, v___x_3342_);
lean_ctor_set(v___x_3344_, 4, v___x_3343_);
lean_ctor_set(v___x_3344_, 5, v___x_3340_);
lean_ctor_set(v___x_3344_, 6, v___x_3343_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7, v___x_3290_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 1, v___x_3290_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 2, v___x_3290_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 3, v_hasTrace_3008_);
v___x_3345_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3346_ = lean_st_mk_ref(v___x_3345_);
lean_inc(v___x_3346_);
v___x_3347_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3321_, v_hasTrace_3008_, v___x_3344_, v___x_3346_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref(v___x_3347_);
v___x_3349_ = lean_st_ref_get(v___x_3346_);
lean_dec(v___x_3346_);
lean_dec(v___x_3349_);
v_a_3302_ = v_a_3348_;
goto v___jp_3301_;
}
else
{
lean_dec(v___x_3346_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3350_; 
v_a_3350_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3350_);
lean_dec_ref(v___x_3347_);
v_a_3302_ = v_a_3350_;
goto v___jp_3301_;
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
v_a_3351_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3347_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3347_);
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
}
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec(v_snd_3322_);
lean_del_object(v___x_3319_);
v___x_3359_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3360_ = lean_box(1);
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3365_, 0, v___x_3359_);
lean_ctor_set(v___x_3365_, 1, v___x_3360_);
lean_ctor_set(v___x_3365_, 2, v___x_3362_);
lean_ctor_set(v___x_3365_, 3, v___x_3363_);
lean_ctor_set(v___x_3365_, 4, v___x_3364_);
lean_ctor_set(v___x_3365_, 5, v___x_3361_);
lean_ctor_set(v___x_3365_, 6, v___x_3364_);
lean_ctor_set_uint8(v___x_3365_, sizeof(void*)*7, v___x_3290_);
lean_ctor_set_uint8(v___x_3365_, sizeof(void*)*7 + 1, v___x_3290_);
lean_ctor_set_uint8(v___x_3365_, sizeof(void*)*7 + 2, v___x_3290_);
lean_ctor_set_uint8(v___x_3365_, sizeof(void*)*7 + 3, v_hasTrace_3008_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3367_ = lean_st_mk_ref(v___x_3366_);
lean_inc(v___x_3367_);
v___x_3368_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3321_, v___x_3365_, v___x_3367_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3370_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref(v___x_3368_);
v___x_3370_ = lean_st_ref_get(v___x_3367_);
lean_dec(v___x_3367_);
lean_dec(v___x_3370_);
v_a_3292_ = v_a_3369_;
goto v___jp_3291_;
}
else
{
lean_dec(v___x_3367_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3371_; 
v_a_3371_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3371_);
lean_dec_ref(v___x_3368_);
v_a_3292_ = v_a_3371_;
goto v___jp_3291_;
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_del_object(v___x_3108_);
v_a_3372_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3368_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3368_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
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
lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_dec(v___x_3316_);
lean_del_object(v___x_3108_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v_name_3003_);
v___x_3381_ = lean_box(v___x_3290_);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
return v___x_3382_;
}
}
else
{
lean_inc_ref(v_options_3007_);
lean_del_object(v___x_3108_);
goto v___jp_3192_;
}
v___jp_3291_:
{
if (lean_obj_tag(v_a_3292_) == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = lean_box(v___x_3290_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3293_);
v___x_3295_ = v___x_3108_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
else
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
lean_dec_ref(v_a_3292_);
v___x_3297_ = lean_box(v_hasTrace_3008_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3297_);
v___x_3299_ = v___x_3108_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
v___jp_3301_:
{
if (lean_obj_tag(v_a_3302_) == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_box(v___x_3290_);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
else
{
lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3312_; 
v_isSharedCheck_3312_ = !lean_is_exclusive(v_a_3302_);
if (v_isSharedCheck_3312_ == 0)
{
lean_object* v_unused_3313_; 
v_unused_3313_ = lean_ctor_get(v_a_3302_, 0);
lean_dec(v_unused_3313_);
v___x_3306_ = v_a_3302_;
v_isShared_3307_ = v_isSharedCheck_3312_;
goto v_resetjp_3305_;
}
else
{
lean_dec(v_a_3302_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3312_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3310_; 
v___x_3308_ = lean_box(v_hasTrace_3008_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set_tag(v___x_3306_, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3308_);
v___x_3310_ = v___x_3306_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
else
{
lean_inc_ref(v_options_3007_);
lean_del_object(v___x_3108_);
goto v___jp_3192_;
}
v___jp_3112_:
{
lean_object* v___x_3116_; double v___x_3117_; double v___x_3118_; double v___x_3119_; double v___x_3120_; double v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; lean_object* v___x_3127_; 
v___x_3116_ = lean_io_mono_nanos_now();
v___x_3117_ = lean_float_of_nat(v___y_3113_);
v___x_3118_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3119_ = lean_float_div(v___x_3117_, v___x_3118_);
v___x_3120_ = lean_float_of_nat(v___x_3116_);
v___x_3121_ = lean_float_div(v___x_3120_, v___x_3118_);
v___x_3122_ = lean_box_float(v___x_3119_);
v___x_3123_ = lean_box_float(v___x_3121_);
v___x_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3122_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_a_3115_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_unbox(v_a_3106_);
lean_dec(v_a_3106_);
v___x_3127_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v___x_3104_, v_hasTrace_3008_, v___x_3111_, v_options_3007_, v___x_3126_, v___y_3114_, v___f_3110_, v___x_3125_, v___y_3004_, v___y_3005_);
lean_dec_ref(v_options_3007_);
return v___x_3127_;
}
v___jp_3128_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_box(v_a_3131_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
v___y_3113_ = v___y_3129_;
v___y_3114_ = v___y_3130_;
v_a_3115_ = v___x_3133_;
goto v___jp_3112_;
}
v___jp_3134_:
{
if (lean_obj_tag(v_a_3138_) == 0)
{
v___y_3129_ = v___y_3135_;
v___y_3130_ = v___y_3137_;
v_a_3131_ = v___y_3136_;
goto v___jp_3128_;
}
else
{
lean_dec_ref(v_a_3138_);
v___y_3129_ = v___y_3135_;
v___y_3130_ = v___y_3137_;
v_a_3131_ = v_hasTrace_3008_;
goto v___jp_3128_;
}
}
v___jp_3139_:
{
if (lean_obj_tag(v_a_3143_) == 0)
{
v___y_3129_ = v___y_3140_;
v___y_3130_ = v___y_3142_;
v_a_3131_ = v___y_3141_;
goto v___jp_3128_;
}
else
{
lean_dec_ref(v_a_3143_);
v___y_3129_ = v___y_3140_;
v___y_3130_ = v___y_3142_;
v_a_3131_ = v_hasTrace_3008_;
goto v___jp_3128_;
}
}
v___jp_3144_:
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_a_3147_);
v___y_3113_ = v___y_3145_;
v___y_3114_ = v___y_3146_;
v_a_3115_ = v___x_3148_;
goto v___jp_3112_;
}
v___jp_3149_:
{
lean_object* v___x_3153_; double v___x_3154_; double v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3153_ = lean_io_get_num_heartbeats();
v___x_3154_ = lean_float_of_nat(v___y_3150_);
v___x_3155_ = lean_float_of_nat(v___x_3153_);
v___x_3156_ = lean_box_float(v___x_3154_);
v___x_3157_ = lean_box_float(v___x_3155_);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_a_3152_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_unbox(v_a_3106_);
lean_dec(v_a_3106_);
v___x_3161_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2(v___x_3104_, v_hasTrace_3008_, v___x_3111_, v_options_3007_, v___x_3160_, v___y_3151_, v___f_3110_, v___x_3159_, v___y_3004_, v___y_3005_);
lean_dec_ref(v_options_3007_);
return v___x_3161_;
}
v___jp_3162_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_box(v_a_3165_);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
v___y_3150_ = v___y_3163_;
v___y_3151_ = v___y_3164_;
v_a_3152_ = v___x_3167_;
goto v___jp_3149_;
}
v___jp_3168_:
{
if (lean_obj_tag(v_a_3173_) == 0)
{
v___y_3163_ = v___y_3169_;
v___y_3164_ = v___y_3172_;
v_a_3165_ = v___y_3171_;
goto v___jp_3162_;
}
else
{
lean_dec_ref(v_a_3173_);
v___y_3163_ = v___y_3169_;
v___y_3164_ = v___y_3172_;
v_a_3165_ = v___y_3170_;
goto v___jp_3162_;
}
}
v___jp_3174_:
{
if (lean_obj_tag(v_a_3178_) == 0)
{
uint8_t v___x_3179_; 
v___x_3179_ = 0;
v___y_3163_ = v___y_3175_;
v___y_3164_ = v___y_3177_;
v_a_3165_ = v___x_3179_;
goto v___jp_3162_;
}
else
{
lean_dec_ref(v_a_3178_);
v___y_3163_ = v___y_3175_;
v___y_3164_ = v___y_3177_;
v_a_3165_ = v___y_3176_;
goto v___jp_3162_;
}
}
v___jp_3180_:
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v_a_3183_);
v___y_3150_ = v___y_3181_;
v___y_3151_ = v___y_3182_;
v_a_3152_ = v___x_3184_;
goto v___jp_3149_;
}
v___jp_3185_:
{
if (lean_obj_tag(v___y_3188_) == 0)
{
lean_object* v_a_3189_; uint8_t v___x_3190_; 
v_a_3189_ = lean_ctor_get(v___y_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref(v___y_3188_);
v___x_3190_ = lean_unbox(v_a_3189_);
lean_dec(v_a_3189_);
v___y_3163_ = v___y_3186_;
v___y_3164_ = v___y_3187_;
v_a_3165_ = v___x_3190_;
goto v___jp_3162_;
}
else
{
lean_object* v_a_3191_; 
v_a_3191_ = lean_ctor_get(v___y_3188_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v___y_3188_);
v___y_3181_ = v___y_3186_;
v___y_3182_ = v___y_3187_;
v_a_3183_ = v_a_3191_;
goto v___jp_3180_;
}
}
v___jp_3192_:
{
lean_object* v___x_3193_; lean_object* v_a_3194_; lean_object* v___x_3195_; uint8_t v___x_3196_; 
v___x_3193_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___redArg(v___y_3005_);
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___x_3193_);
v___x_3195_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3196_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_3007_, v___x_3195_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_env_3199_; lean_object* v___x_3200_; 
lean_dec_ref(v___f_3002_);
v___x_3197_ = lean_io_mono_nanos_now();
v___x_3198_ = lean_st_ref_get(v___y_3005_);
v_env_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc_ref(v_env_3199_);
lean_dec(v___x_3198_);
lean_inc(v_name_3003_);
v___x_3200_ = l_Lean_Meta_declFromEqLikeName(v_env_3199_, v_name_3003_);
if (lean_obj_tag(v___x_3200_) == 1)
{
lean_object* v_val_3201_; lean_object* v_fst_3202_; lean_object* v_snd_3203_; lean_object* v___x_3204_; lean_object* v_env_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; 
v_val_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_val_3201_);
lean_dec_ref(v___x_3200_);
v_fst_3202_ = lean_ctor_get(v_val_3201_, 0);
lean_inc(v_fst_3202_);
v_snd_3203_ = lean_ctor_get(v_val_3201_, 1);
lean_inc(v_snd_3203_);
lean_dec(v_val_3201_);
v___x_3204_ = lean_st_ref_get(v___y_3005_);
v_env_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc_ref(v_env_3205_);
lean_dec(v___x_3204_);
lean_inc(v_snd_3203_);
lean_inc(v_fst_3202_);
v___x_3206_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3205_, v_fst_3202_, v_snd_3203_);
v___x_3207_ = lean_name_eq(v_name_3003_, v___x_3206_);
lean_dec(v___x_3206_);
lean_dec(v_name_3003_);
if (v___x_3207_ == 0)
{
lean_dec(v_snd_3203_);
lean_dec(v_fst_3202_);
v___y_3129_ = v___x_3197_;
v___y_3130_ = v_a_3194_;
v_a_3131_ = v___x_3196_;
goto v___jp_3128_;
}
else
{
uint8_t v___x_3208_; 
lean_inc(v_snd_3203_);
v___x_3208_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3203_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___x_3209_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3210_ = lean_string_dec_eq(v_snd_3203_, v___x_3209_);
lean_dec(v_snd_3203_);
if (v___x_3210_ == 0)
{
lean_dec(v_fst_3202_);
v___y_3129_ = v___x_3197_;
v___y_3130_ = v_a_3194_;
v_a_3131_ = v___x_3196_;
goto v___jp_3128_;
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3211_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3212_ = lean_box(1);
v___x_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3215_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3216_ = lean_box(0);
v___x_3217_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3217_, 0, v___x_3211_);
lean_ctor_set(v___x_3217_, 1, v___x_3212_);
lean_ctor_set(v___x_3217_, 2, v___x_3214_);
lean_ctor_set(v___x_3217_, 3, v___x_3215_);
lean_ctor_set(v___x_3217_, 4, v___x_3216_);
lean_ctor_set(v___x_3217_, 5, v___x_3213_);
lean_ctor_set(v___x_3217_, 6, v___x_3216_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7, v___x_3196_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 1, v___x_3196_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 2, v___x_3196_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 3, v_hasTrace_3008_);
v___x_3218_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3219_ = lean_st_mk_ref(v___x_3218_);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___x_3219_);
v___x_3220_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3202_, v_hasTrace_3008_, v___x_3217_, v___x_3219_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3222_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___x_3220_);
v___x_3222_ = lean_st_ref_get(v___x_3219_);
lean_dec(v___x_3219_);
lean_dec(v___x_3222_);
v___y_3140_ = v___x_3197_;
v___y_3141_ = v___x_3196_;
v___y_3142_ = v_a_3194_;
v_a_3143_ = v_a_3221_;
goto v___jp_3139_;
}
else
{
lean_dec(v___x_3219_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3223_; 
v_a_3223_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3223_);
lean_dec_ref(v___x_3220_);
v___y_3140_ = v___x_3197_;
v___y_3141_ = v___x_3196_;
v___y_3142_ = v_a_3194_;
v_a_3143_ = v_a_3223_;
goto v___jp_3139_;
}
else
{
lean_object* v_a_3224_; 
v_a_3224_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3224_);
lean_dec_ref(v___x_3220_);
v___y_3145_ = v___x_3197_;
v___y_3146_ = v_a_3194_;
v_a_3147_ = v_a_3224_;
goto v___jp_3144_;
}
}
}
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_dec(v_snd_3203_);
v___x_3225_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3226_ = lean_box(1);
v___x_3227_ = lean_unsigned_to_nat(0u);
v___x_3228_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3229_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3230_ = lean_box(0);
v___x_3231_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3231_, 0, v___x_3225_);
lean_ctor_set(v___x_3231_, 1, v___x_3226_);
lean_ctor_set(v___x_3231_, 2, v___x_3228_);
lean_ctor_set(v___x_3231_, 3, v___x_3229_);
lean_ctor_set(v___x_3231_, 4, v___x_3230_);
lean_ctor_set(v___x_3231_, 5, v___x_3227_);
lean_ctor_set(v___x_3231_, 6, v___x_3230_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*7, v___x_3196_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*7 + 1, v___x_3196_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*7 + 2, v___x_3196_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*7 + 3, v_hasTrace_3008_);
v___x_3232_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3233_ = lean_st_mk_ref(v___x_3232_);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___x_3233_);
v___x_3234_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3202_, v___x_3231_, v___x_3233_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref(v___x_3234_);
v___x_3236_ = lean_st_ref_get(v___x_3233_);
lean_dec(v___x_3233_);
lean_dec(v___x_3236_);
v___y_3135_ = v___x_3197_;
v___y_3136_ = v___x_3196_;
v___y_3137_ = v_a_3194_;
v_a_3138_ = v_a_3235_;
goto v___jp_3134_;
}
else
{
lean_dec(v___x_3233_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3237_; 
v_a_3237_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3237_);
lean_dec_ref(v___x_3234_);
v___y_3135_ = v___x_3197_;
v___y_3136_ = v___x_3196_;
v___y_3137_ = v_a_3194_;
v_a_3138_ = v_a_3237_;
goto v___jp_3134_;
}
else
{
lean_object* v_a_3238_; 
v_a_3238_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3238_);
lean_dec_ref(v___x_3234_);
v___y_3145_ = v___x_3197_;
v___y_3146_ = v_a_3194_;
v_a_3147_ = v_a_3238_;
goto v___jp_3144_;
}
}
}
}
}
else
{
lean_dec(v___x_3200_);
lean_dec(v_name_3003_);
v___y_3129_ = v___x_3197_;
v___y_3130_ = v_a_3194_;
v_a_3131_ = v___x_3196_;
goto v___jp_3128_;
}
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v_env_3241_; lean_object* v___x_3242_; 
v___x_3239_ = lean_io_get_num_heartbeats();
v___x_3240_ = lean_st_ref_get(v___y_3005_);
v_env_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc_ref(v_env_3241_);
lean_dec(v___x_3240_);
lean_inc(v_name_3003_);
v___x_3242_ = l_Lean_Meta_declFromEqLikeName(v_env_3241_, v_name_3003_);
if (lean_obj_tag(v___x_3242_) == 1)
{
lean_object* v_val_3243_; lean_object* v_fst_3244_; lean_object* v_snd_3245_; lean_object* v___x_3246_; lean_object* v_env_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v_val_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_val_3243_);
lean_dec_ref(v___x_3242_);
v_fst_3244_ = lean_ctor_get(v_val_3243_, 0);
lean_inc(v_fst_3244_);
v_snd_3245_ = lean_ctor_get(v_val_3243_, 1);
lean_inc(v_snd_3245_);
lean_dec(v_val_3243_);
v___x_3246_ = lean_st_ref_get(v___y_3005_);
v_env_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc_ref(v_env_3247_);
lean_dec(v___x_3246_);
lean_inc(v_snd_3245_);
lean_inc(v_fst_3244_);
v___x_3248_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3247_, v_fst_3244_, v_snd_3245_);
v___x_3249_ = lean_name_eq(v_name_3003_, v___x_3248_);
lean_dec(v___x_3248_);
lean_dec(v_name_3003_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec(v_snd_3245_);
lean_dec(v_fst_3244_);
v___x_3250_ = lean_box(0);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
v___x_3251_ = lean_apply_4(v___f_3002_, v___x_3250_, v___y_3004_, v___y_3005_, lean_box(0));
v___y_3186_ = v___x_3239_;
v___y_3187_ = v_a_3194_;
v___y_3188_ = v___x_3251_;
goto v___jp_3185_;
}
else
{
uint8_t v___x_3252_; 
lean_inc(v_snd_3245_);
v___x_3252_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3245_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3254_ = lean_string_dec_eq(v_snd_3245_, v___x_3253_);
lean_dec(v_snd_3245_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_dec(v_fst_3244_);
v___x_3255_ = lean_box(0);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
v___x_3256_ = lean_apply_4(v___f_3002_, v___x_3255_, v___y_3004_, v___y_3005_, lean_box(0));
v___y_3186_ = v___x_3239_;
v___y_3187_ = v_a_3194_;
v___y_3188_ = v___x_3256_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec_ref(v___f_3002_);
v___x_3257_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3258_ = lean_box(1);
v___x_3259_ = lean_unsigned_to_nat(0u);
v___x_3260_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3261_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3262_ = lean_box(0);
v___x_3263_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3263_, 0, v___x_3257_);
lean_ctor_set(v___x_3263_, 1, v___x_3258_);
lean_ctor_set(v___x_3263_, 2, v___x_3260_);
lean_ctor_set(v___x_3263_, 3, v___x_3261_);
lean_ctor_set(v___x_3263_, 4, v___x_3262_);
lean_ctor_set(v___x_3263_, 5, v___x_3259_);
lean_ctor_set(v___x_3263_, 6, v___x_3262_);
lean_ctor_set_uint8(v___x_3263_, sizeof(void*)*7, v___x_3252_);
lean_ctor_set_uint8(v___x_3263_, sizeof(void*)*7 + 1, v___x_3252_);
lean_ctor_set_uint8(v___x_3263_, sizeof(void*)*7 + 2, v___x_3252_);
lean_ctor_set_uint8(v___x_3263_, sizeof(void*)*7 + 3, v___x_3196_);
v___x_3264_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3265_ = lean_st_mk_ref(v___x_3264_);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___x_3265_);
v___x_3266_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3244_, v___x_3196_, v___x_3263_, v___x_3265_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref(v___x_3266_);
v___x_3268_ = lean_st_ref_get(v___x_3265_);
lean_dec(v___x_3265_);
lean_dec(v___x_3268_);
v___y_3169_ = v___x_3239_;
v___y_3170_ = v___x_3196_;
v___y_3171_ = v___x_3252_;
v___y_3172_ = v_a_3194_;
v_a_3173_ = v_a_3267_;
goto v___jp_3168_;
}
else
{
lean_dec(v___x_3265_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3269_; 
v_a_3269_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3266_);
v___y_3169_ = v___x_3239_;
v___y_3170_ = v___x_3196_;
v___y_3171_ = v___x_3252_;
v___y_3172_ = v_a_3194_;
v_a_3173_ = v_a_3269_;
goto v___jp_3168_;
}
else
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3266_);
v___y_3181_ = v___x_3239_;
v___y_3182_ = v_a_3194_;
v_a_3183_ = v_a_3270_;
goto v___jp_3180_;
}
}
}
}
else
{
lean_object* v___x_3271_; uint8_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec(v_snd_3245_);
lean_dec_ref(v___f_3002_);
v___x_3271_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3272_ = 0;
v___x_3273_ = lean_box(1);
v___x_3274_ = lean_unsigned_to_nat(0u);
v___x_3275_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3276_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3277_ = lean_box(0);
v___x_3278_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3278_, 0, v___x_3271_);
lean_ctor_set(v___x_3278_, 1, v___x_3273_);
lean_ctor_set(v___x_3278_, 2, v___x_3275_);
lean_ctor_set(v___x_3278_, 3, v___x_3276_);
lean_ctor_set(v___x_3278_, 4, v___x_3277_);
lean_ctor_set(v___x_3278_, 5, v___x_3274_);
lean_ctor_set(v___x_3278_, 6, v___x_3277_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7, v___x_3272_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 1, v___x_3272_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 2, v___x_3272_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 3, v___x_3196_);
v___x_3279_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3280_ = lean_st_mk_ref(v___x_3279_);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___x_3280_);
v___x_3281_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3244_, v___x_3278_, v___x_3280_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3283_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = lean_st_ref_get(v___x_3280_);
lean_dec(v___x_3280_);
lean_dec(v___x_3283_);
v___y_3175_ = v___x_3239_;
v___y_3176_ = v___x_3196_;
v___y_3177_ = v_a_3194_;
v_a_3178_ = v_a_3282_;
goto v___jp_3174_;
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
v___y_3175_ = v___x_3239_;
v___y_3176_ = v___x_3196_;
v___y_3177_ = v_a_3194_;
v_a_3178_ = v_a_3284_;
goto v___jp_3174_;
}
else
{
lean_object* v_a_3285_; 
v_a_3285_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3285_);
lean_dec_ref(v___x_3281_);
v___y_3181_ = v___x_3239_;
v___y_3182_ = v_a_3194_;
v_a_3183_ = v_a_3285_;
goto v___jp_3180_;
}
}
}
}
}
else
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_dec(v___x_3242_);
lean_dec(v_name_3003_);
v___x_3286_ = lean_box(0);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
v___x_3287_ = lean_apply_4(v___f_3002_, v___x_3286_, v___y_3004_, v___y_3005_, lean_box(0));
v___y_3186_ = v___x_3239_;
v___y_3187_ = v_a_3194_;
v___y_3188_ = v___x_3287_;
goto v___jp_3185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3384_, lean_object* v_name_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3384_, v_name_3385_, v___y_3386_, v___y_3387_);
return v_res_3389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = lean_unsigned_to_nat(3137104340u);
v___x_3434_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3435_ = l_Lean_Name_num___override(v___x_3434_, v___x_3433_);
return v___x_3435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3438_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3439_ = l_Lean_Name_str___override(v___x_3438_, v___x_3437_);
return v___x_3439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3442_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3443_ = l_Lean_Name_str___override(v___x_3442_, v___x_3441_);
return v___x_3443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_unsigned_to_nat(2u);
v___x_3445_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3446_ = l_Lean_Name_num___override(v___x_3445_, v___x_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3448_; lean_object* v___x_3449_; 
v___f_3448_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3449_ = l_Lean_registerReservedNameAction(v___f_3448_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v___x_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec_ref(v___x_3449_);
v___x_3450_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_3451_ = 0;
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3453_ = l_Lean_registerTraceClass(v___x_3450_, v___x_3451_, v___x_3452_);
return v___x_3453_;
}
else
{
return v___x_3449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_00_u03b1_3456_, lean_object* v_x_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___redArg(v_x_3457_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_00_u03b1_3462_, lean_object* v_x_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__2_spec__4(v_00_u03b1_3462_, v_x_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
return v_res_3467_;
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
