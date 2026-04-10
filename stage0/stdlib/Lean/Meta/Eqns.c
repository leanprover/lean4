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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eqns"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nonrecursive"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 23, 21, 28, 3, 196, 180, 100)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(1, 23, 146, 109, 99, 186, 103, 88)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "Create fine-grained equational lemmas even for non-recursive definitions."};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2026-03-30"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 217, 222, 73, 223, 67, 131, 25)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(156, 7, 83, 198, 209, 69, 31, 191)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_eqns_nonrecursive;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "deepRecursiveSplit"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 23, 21, 28, 3, 196, 180, 100)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(167, 67, 13, 105, 163, 80, 199, 218)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 339, .m_capacity = 339, .m_length = 338, .m_data = "Create equational lemmas for recursive functions like for non-recursive functions. If disabled, match statements in recursive function definitions that do not contain recursive calls do not cause further splits in the equational lemmas. This was the behavior before Lean 4.12, and the purpose of this option is to help migrating old code."};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 217, 222, 73, 223, 67, 131, 25)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(226, 35, 35, 130, 249, 93, 79, 68)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_generateEagerEqns___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_generateEagerEqns___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 70, 141, 178, 157, 107, 140, 91)}};
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
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Eqns"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 217, 145, 26, 133, 108, 104, 10)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(27, 2, 5, 79, 97, 142, 74, 217)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 112, 146, 108, 241, 250, 100, 162)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 0, 196, 176, 89, 93, 16, 10)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 31, 160, 103, 40, 58, 110, 116)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 147, 153, 14, 107, 3, 39, 172)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 114, 185, 94, 205, 199, 191, 156)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 255, 177, 29, 188, 255, 188, 249)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_));
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_));
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_));
v___x_65_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4____boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_));
v___x_87_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_));
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_));
v___x_89_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v___x_86_, v___x_87_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4____boxed(lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_();
return v_res_91_;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__0(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_92_ = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
v___x_93_ = l_Lean_Meta_backward_eqns_nonrecursive;
v___x_94_ = lean_unsigned_to_nat(2u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_array_push(v___x_95_, v___x_93_);
v___x_97_ = lean_array_push(v___x_96_, v___x_92_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_Meta_eqnAffectingOptions___closed__0, &l_Lean_Meta_eqnAffectingOptions___closed__0_once, _init_l_Lean_Meta_eqnAffectingOptions___closed__0);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_106_ = lean_string_utf8_byte_size(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_108_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_109_ = lean_string_utf8_byte_size(v_s_107_);
v___x_110_ = lean_obj_once(&l_Lean_Meta_isEqnReservedNameSuffix___closed__0, &l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0);
v___x_111_ = lean_nat_dec_le(v___x_110_, v___x_109_);
if (v___x_111_ == 0)
{
lean_dec_ref(v_s_107_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_string_memcmp(v_s_107_, v___x_108_, v___x_112_, v___x_112_, v___x_110_);
if (v___x_113_ == 0)
{
lean_dec_ref(v_s_107_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_114_ = lean_unsigned_to_nat(3u);
lean_inc_ref(v_s_107_);
v___x_115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_115_, 0, v_s_107_);
lean_ctor_set(v___x_115_, 1, v___x_112_);
lean_ctor_set(v___x_115_, 2, v___x_109_);
v___x_116_ = l_String_Slice_Pos_nextn(v___x_115_, v___x_112_, v___x_114_);
lean_dec_ref(v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v_s_107_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
lean_ctor_set(v___x_117_, 2, v___x_109_);
v___x_118_ = l_String_Slice_isNat(v___x_117_);
lean_dec_ref(v___x_117_);
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_126_){
_start:
{
uint8_t v___y_128_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_131_ = lean_string_dec_eq(v_s_126_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_133_ = lean_string_dec_eq(v_s_126_, v___x_132_);
v___y_128_ = v___x_133_;
goto v___jp_127_;
}
else
{
v___y_128_ = v___x_131_;
goto v___jp_127_;
}
v___jp_127_:
{
if (v___y_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_126_);
return v___x_129_;
}
else
{
lean_dec_ref(v_s_126_);
return v___y_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_Meta_isEqnLikeSuffix(v_s_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_140_, lean_object* v_env_141_, lean_object* v_as_x27_142_, lean_object* v_b_143_){
_start:
{
if (lean_obj_tag(v_as_x27_142_) == 0)
{
lean_dec_ref(v_env_141_);
lean_dec_ref(v_str_140_);
lean_inc_ref(v_b_143_);
return v_b_143_;
}
else
{
lean_object* v_head_144_; lean_object* v_tail_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_165_; 
v_head_144_ = lean_ctor_get(v_as_x27_142_, 0);
v_tail_145_ = lean_ctor_get(v_as_x27_142_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_as_x27_142_);
if (v_isSharedCheck_165_ == 0)
{
v___x_147_ = v_as_x27_142_;
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_tail_145_);
lean_inc(v_head_144_);
lean_dec(v_as_x27_142_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___y_152_; uint8_t v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_149_ = lean_box(0);
v___x_150_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_160_ = 0;
lean_inc_ref(v_env_141_);
v___x_161_ = l_Lean_Environment_setExporting(v_env_141_, v___x_160_);
lean_inc(v_head_144_);
v___x_162_ = l_Lean_Environment_isSafeDefinition(v___x_161_, v_head_144_);
if (v___x_162_ == 0)
{
v___y_152_ = v___x_162_;
goto v___jp_151_;
}
else
{
uint8_t v___x_163_; 
lean_inc(v_head_144_);
lean_inc_ref(v_env_141_);
v___x_163_ = lean_is_matcher(v_env_141_, v_head_144_);
if (v___x_163_ == 0)
{
v___y_152_ = v___x_162_;
goto v___jp_151_;
}
else
{
lean_del_object(v___x_147_);
lean_dec(v_head_144_);
v_as_x27_142_ = v_tail_145_;
v_b_143_ = v___x_150_;
goto _start;
}
}
v___jp_151_:
{
if (v___y_152_ == 0)
{
lean_del_object(v___x_147_);
lean_dec(v_head_144_);
v_as_x27_142_ = v_tail_145_;
v_b_143_ = v___x_150_;
goto _start;
}
else
{
lean_object* v___x_155_; 
lean_dec(v_tail_145_);
lean_dec_ref(v_env_141_);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 0);
lean_ctor_set(v___x_147_, 1, v_str_140_);
v___x_155_ = v___x_147_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_head_144_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_str_140_);
v___x_155_ = v_reuseFailAlloc_159_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_149_);
return v___x_158_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_166_, lean_object* v_env_167_, lean_object* v_as_x27_168_, lean_object* v_b_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_166_, v_env_167_, v_as_x27_168_, v_b_169_);
lean_dec_ref(v_b_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_171_, lean_object* v_name_172_){
_start:
{
if (lean_obj_tag(v_name_172_) == 1)
{
lean_object* v_pre_173_; lean_object* v_str_174_; uint8_t v___x_175_; 
v_pre_173_ = lean_ctor_get(v_name_172_, 0);
lean_inc(v_pre_173_);
v_str_174_ = lean_ctor_get(v_name_172_, 1);
lean_inc_ref_n(v_str_174_, 2);
lean_dec_ref(v_name_172_);
v___x_175_ = l_Lean_Meta_isEqnLikeSuffix(v_str_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec_ref(v_str_174_);
lean_dec(v_pre_173_);
lean_dec_ref(v_env_171_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_fst_184_; 
lean_inc(v_pre_173_);
v___x_177_ = l_Lean_privateToUserName(v_pre_173_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v_pre_173_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_box(0);
v___x_182_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_183_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_174_, v_env_171_, v___x_180_, v___x_182_);
v_fst_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_fst_184_);
lean_dec_ref(v___x_183_);
if (lean_obj_tag(v_fst_184_) == 0)
{
return v___x_181_;
}
else
{
lean_object* v_val_185_; 
v_val_185_ = lean_ctor_get(v_fst_184_, 0);
lean_inc(v_val_185_);
lean_dec_ref(v_fst_184_);
return v_val_185_;
}
}
}
else
{
lean_object* v___x_186_; 
lean_dec(v_name_172_);
lean_dec_ref(v_env_171_);
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_187_, lean_object* v_env_188_, lean_object* v_as_189_, lean_object* v_as_x27_190_, lean_object* v_b_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_187_, v_env_188_, v_as_x27_190_, v_b_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_194_, lean_object* v_env_195_, lean_object* v_as_196_, lean_object* v_as_x27_197_, lean_object* v_b_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_194_, v_env_195_, v_as_196_, v_as_x27_197_, v_b_198_, v_a_199_);
lean_dec_ref(v_b_198_);
lean_dec(v_as_196_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_201_, lean_object* v_declName_202_, lean_object* v_suffix_203_){
_start:
{
lean_object* v___x_207_; uint8_t v_isModule_208_; 
v___x_207_ = l_Lean_Environment_header(v_env_201_);
v_isModule_208_ = lean_ctor_get_uint8(v___x_207_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_207_);
if (v_isModule_208_ == 0)
{
lean_object* v_name_209_; 
lean_dec_ref(v_env_201_);
v_name_209_ = l_Lean_Name_str___override(v_declName_202_, v_suffix_203_);
return v_name_209_;
}
else
{
uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = 0;
lean_inc_ref(v_env_201_);
v___x_211_ = l_Lean_Environment_setExporting(v_env_201_, v_isModule_208_);
lean_inc(v_declName_202_);
v___x_212_ = l_Lean_Environment_find_x3f(v___x_211_, v_declName_202_, v___x_210_);
if (lean_obj_tag(v___x_212_) == 0)
{
goto v___jp_204_;
}
else
{
lean_object* v_val_213_; uint8_t v___x_214_; 
v_val_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_val_213_);
lean_dec_ref(v___x_212_);
v___x_214_ = l_Lean_ConstantInfo_hasValue(v_val_213_, v___x_210_);
lean_dec(v_val_213_);
if (v___x_214_ == 0)
{
goto v___jp_204_;
}
else
{
lean_object* v_name_215_; 
lean_dec_ref(v_env_201_);
v_name_215_ = l_Lean_Name_str___override(v_declName_202_, v_suffix_203_);
return v_name_215_;
}
}
}
v___jp_204_:
{
lean_object* v_name_205_; lean_object* v___x_206_; 
v_name_205_ = l_Lean_Name_str___override(v_declName_202_, v_suffix_203_);
v___x_206_ = l_Lean_mkPrivateName(v_env_201_, v_name_205_);
lean_dec_ref(v_env_201_);
return v___x_206_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_216_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_ctor_set(v___x_221_, 3, v___x_220_);
lean_ctor_set(v___x_221_, 4, v___x_219_);
lean_ctor_set(v___x_221_, 5, v___x_219_);
lean_ctor_set(v___x_221_, 6, v___x_219_);
lean_ctor_set(v___x_221_, 7, v___x_219_);
lean_ctor_set(v___x_221_, 8, v___x_219_);
lean_ctor_set(v___x_221_, 9, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_unsigned_to_nat(32u);
v___x_223_ = lean_mk_empty_array_with_capacity(v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_225_ = ((size_t)5ULL);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_unsigned_to_nat(32u);
v___x_228_ = lean_mk_empty_array_with_capacity(v___x_227_);
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_230_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_226_);
lean_ctor_set(v___x_230_, 3, v___x_226_);
lean_ctor_set_usize(v___x_230_, 4, v___x_225_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = lean_box(1);
v___x_232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_233_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_231_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; lean_object* v_env_240_; lean_object* v_options_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_239_ = lean_st_ref_get(v___y_237_);
v_env_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_env_240_);
lean_dec(v___x_239_);
v_options_241_ = lean_ctor_get(v___y_236_, 2);
v___x_242_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_243_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_241_);
v___x_244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_244_, 0, v_env_240_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
lean_ctor_set(v___x_244_, 2, v___x_243_);
lean_ctor_set(v___x_244_, 3, v_options_241_);
v___x_245_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_msgData_235_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_ref_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_ref_256_ = lean_ctor_get(v___y_253_, 5);
v___x_257_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_252_, v___y_253_, v___y_254_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
lean_inc(v_ref_256_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_ref_256_);
lean_ctor_set(v___x_262_, 1, v_a_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 1);
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_271_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_277_ = l_Lean_stringToMessageData(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_281_, lean_object* v_reservedName_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_286_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_287_ = 0;
v___x_288_ = l_Lean_MessageData_ofConstName(v_declName_281_, v___x_287_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_286_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = 1;
v___x_293_ = l_Lean_MessageData_ofConstName(v_reservedName_282_, v___x_292_);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_291_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_296_, v___y_283_, v___y_284_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_298_, lean_object* v_reservedName_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_298_, v_reservedName_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_304_, lean_object* v_suffix_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_env_310_; lean_object* v_reservedName_311_; uint8_t v___x_312_; uint8_t v___x_313_; 
v___x_309_ = lean_st_ref_get(v___y_307_);
v_env_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_env_310_);
lean_dec(v___x_309_);
lean_inc(v_declName_304_);
v_reservedName_311_ = l_Lean_Name_str___override(v_declName_304_, v_suffix_305_);
v___x_312_ = 1;
lean_inc(v_reservedName_311_);
v___x_313_ = l_Lean_Environment_contains(v_env_310_, v_reservedName_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_reservedName_311_);
lean_dec(v_declName_304_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_304_, v_reservedName_311_, v___y_306_, v___y_307_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_317_, lean_object* v_suffix_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_317_, v_suffix_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_323_);
v___x_328_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_323_, v___x_327_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v___x_328_);
v___x_329_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_323_);
v___x_330_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_323_, v___x_329_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v___x_330_);
v___x_331_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_332_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_323_, v___x_331_, v_a_324_, v_a_325_);
return v___x_332_;
}
else
{
lean_dec(v_declName_323_);
return v___x_330_;
}
}
else
{
lean_dec(v_declName_323_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_338_, lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_339_, v___y_340_, v___y_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_344_, v_msg_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_349_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_350_, lean_object* v_n_351_){
_start:
{
lean_object* v___x_352_; 
lean_inc(v_n_351_);
lean_inc_ref(v_env_350_);
v___x_352_ = l_Lean_Meta_declFromEqLikeName(v_env_350_, v_n_351_);
if (lean_obj_tag(v___x_352_) == 1)
{
lean_object* v_val_353_; lean_object* v_fst_354_; lean_object* v_snd_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_val_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_val_353_);
lean_dec_ref(v___x_352_);
v_fst_354_ = lean_ctor_get(v_val_353_, 0);
lean_inc(v_fst_354_);
v_snd_355_ = lean_ctor_get(v_val_353_, 1);
lean_inc(v_snd_355_);
lean_dec(v_val_353_);
v___x_356_ = l_Lean_Meta_mkEqLikeNameFor(v_env_350_, v_fst_354_, v_snd_355_);
v___x_357_ = lean_name_eq(v_n_351_, v___x_356_);
lean_dec(v___x_356_);
lean_dec(v_n_351_);
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
lean_dec(v___x_352_);
lean_dec(v_n_351_);
lean_dec_ref(v_env_350_);
v___x_358_ = 0;
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_359_, lean_object* v_n_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_359_, v_n_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_365_; lean_object* v___x_366_; 
v___f_365_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_366_ = l_Lean_registerReservedNamePredicate(v___f_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_box(0);
v___x_371_ = lean_st_mk_ref(v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_374_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_377_ = lean_mk_io_user_error(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_initializing();
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_397_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_397_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_397_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_397_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; 
v___x_385_ = lean_unbox(v_a_381_);
lean_dec(v_a_381_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec_ref(v_f_378_);
v___x_386_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 1);
lean_ctor_set(v___x_383_, 0, v___x_386_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_390_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_391_ = lean_st_ref_take(v___x_390_);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v_f_378_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_st_ref_set(v___x_390_, v___x_392_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_393_);
v___x_395_ = v___x_383_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
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
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_f_378_);
v_a_398_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_380_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_380_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_registerGetEqnsFn(v_f_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_419_; lean_object* v_env_420_; uint8_t v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_st_ref_get(v_a_413_);
v_env_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_env_420_);
lean_dec(v___x_419_);
v___x_421_ = 0;
lean_inc(v_declName_409_);
v___x_422_ = l_Lean_Environment_findAsync_x3f(v_env_420_, v_declName_409_, v___x_421_);
if (lean_obj_tag(v___x_422_) == 1)
{
lean_object* v_val_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_454_; 
v_val_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_454_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_454_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_val_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_454_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
uint8_t v_kind_427_; 
v_kind_427_ = lean_ctor_get_uint8(v_val_423_, sizeof(void*)*3);
if (v_kind_427_ == 0)
{
lean_object* v_sig_428_; lean_object* v___x_429_; lean_object* v_env_430_; uint8_t v___x_431_; 
v_sig_428_ = lean_ctor_get(v_val_423_, 1);
lean_inc_ref(v_sig_428_);
lean_dec(v_val_423_);
v___x_429_ = lean_st_ref_get(v_a_413_);
v_env_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_env_430_);
lean_dec(v___x_429_);
v___x_431_ = lean_is_matcher(v_env_430_, v_declName_409_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v_type_433_; lean_object* v___x_434_; 
lean_del_object(v___x_425_);
v___x_432_ = lean_task_get_own(v_sig_428_);
v_type_433_ = lean_ctor_get(v___x_432_, 2);
lean_inc_ref(v_type_433_);
lean_dec(v___x_432_);
v___x_434_ = l_Lean_Meta_isProp(v_type_433_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_449_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_449_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_449_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_449_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; 
v___x_439_ = lean_unbox(v_a_435_);
lean_dec(v_a_435_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = 1;
v___x_441_ = lean_box(v___x_440_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_441_);
v___x_443_ = v___x_437_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_box(v___x_431_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_445_);
v___x_447_ = v___x_437_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
return v___x_434_;
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec_ref(v_sig_428_);
v___x_450_ = lean_box(v___x_421_);
if (v_isShared_426_ == 0)
{
lean_ctor_set_tag(v___x_425_, 0);
lean_ctor_set(v___x_425_, 0, v___x_450_);
v___x_452_ = v___x_425_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_del_object(v___x_425_);
lean_dec(v_val_423_);
lean_dec(v_declName_409_);
goto v___jp_415_;
}
}
}
else
{
lean_dec(v___x_422_);
lean_dec(v_declName_409_);
goto v___jp_415_;
}
v___jp_415_:
{
uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = 0;
v___x_417_ = lean_box(v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
return v_res_461_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_470_);
return v_res_472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_473_; lean_object* v___f_474_; 
v___x_473_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_474_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_474_, 0, v___x_473_);
return v___f_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___f_476_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_box(1);
v___x_479_ = l_Lean_registerEnvExtension___redArg(v___f_476_, v___x_477_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_env_486_; lean_object* v_toConstantVal_487_; lean_object* v_value_488_; lean_object* v_all_489_; uint8_t v___y_491_; lean_object* v_type_499_; uint8_t v___x_500_; 
v___x_485_ = lean_st_ref_get(v___y_483_);
v_env_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref_n(v_env_486_, 2);
lean_dec(v___x_485_);
v_toConstantVal_487_ = lean_ctor_get(v_thm_482_, 0);
v_value_488_ = lean_ctor_get(v_thm_482_, 1);
v_all_489_ = lean_ctor_get(v_thm_482_, 2);
v_type_499_ = lean_ctor_get(v_toConstantVal_487_, 2);
v___x_500_ = l_Lean_Environment_hasUnsafe(v_env_486_, v_type_499_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
v___x_501_ = l_Lean_Environment_hasUnsafe(v_env_486_, v_value_488_);
v___y_491_ = v___x_501_;
goto v___jp_490_;
}
else
{
lean_dec_ref(v_env_486_);
v___y_491_ = v___x_500_;
goto v___jp_490_;
}
v___jp_490_:
{
if (v___y_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_492_, 0, v_thm_482_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_inc(v_all_489_);
lean_inc_ref(v_value_488_);
lean_inc_ref(v_toConstantVal_487_);
lean_dec_ref(v_thm_482_);
v___x_494_ = lean_box(0);
v___x_495_ = 0;
v___x_496_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_496_, 0, v_toConstantVal_487_);
lean_ctor_set(v___x_496_, 1, v_value_488_);
lean_ctor_set(v___x_496_, 2, v___x_494_);
lean_ctor_set(v___x_496_, 3, v_all_489_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*4, v___x_495_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_502_, v___y_503_);
lean_dec(v___y_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_506_, v___y_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_520_, lean_object* v_b_521_, lean_object* v_c_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
lean_inc(v___y_526_);
lean_inc_ref(v___y_525_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
v___x_528_ = lean_apply_7(v_k_520_, v_b_521_, v_c_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, lean_box(0));
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_529_, lean_object* v_b_530_, lean_object* v_c_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_529_, v_b_530_, v_c_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_538_, lean_object* v_k_539_, uint8_t v_cleanupAnnotations_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___f_546_; uint8_t v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___f_546_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_546_, 0, v_k_539_);
v___x_547_ = 1;
v___x_548_ = 0;
v___x_549_ = lean_box(0);
v___x_550_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_538_, v___x_547_, v___x_548_, v___x_547_, v___x_548_, v___x_549_, v___f_546_, v_cleanupAnnotations_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
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
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_a_559_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_550_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_550_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_567_, lean_object* v_k_568_, lean_object* v_cleanupAnnotations_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_575_; lean_object* v_res_576_; 
v_cleanupAnnotations_boxed_575_ = lean_unbox(v_cleanupAnnotations_569_);
v_res_576_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_567_, v_k_568_, v_cleanupAnnotations_boxed_575_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_577_, lean_object* v_e_578_, lean_object* v_k_579_, uint8_t v_cleanupAnnotations_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_578_, v_k_579_, v_cleanupAnnotations_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_587_, lean_object* v_e_588_, lean_object* v_k_589_, lean_object* v_cleanupAnnotations_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_596_; lean_object* v_res_597_; 
v_cleanupAnnotations_boxed_596_ = lean_unbox(v_cleanupAnnotations_590_);
v_res_597_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_587_, v_e_588_, v_k_589_, v_cleanupAnnotations_boxed_596_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
if (lean_obj_tag(v_a_598_) == 0)
{
lean_object* v___x_600_; 
v___x_600_ = l_List_reverse___redArg(v_a_599_);
return v___x_600_;
}
else
{
lean_object* v_head_601_; lean_object* v_tail_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_611_; 
v_head_601_ = lean_ctor_get(v_a_598_, 0);
v_tail_602_ = lean_ctor_get(v_a_598_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_a_598_);
if (v_isSharedCheck_611_ == 0)
{
v___x_604_ = v_a_598_;
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_tail_602_);
lean_inc(v_head_601_);
lean_dec(v_a_598_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = l_Lean_mkLevelParam(v_head_601_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v_a_599_);
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_599_);
v___x_608_ = v_reuseFailAlloc_610_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
v_a_598_ = v_tail_602_;
v_a_599_ = v___x_608_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_612_, lean_object* v_name_613_, lean_object* v_xs_614_, lean_object* v_body_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_name_621_; lean_object* v_levelParams_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_692_; 
v_name_621_ = lean_ctor_get(v_toConstantVal_612_, 0);
v_levelParams_622_ = lean_ctor_get(v_toConstantVal_612_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_toConstantVal_612_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v_toConstantVal_612_, 2);
lean_dec(v_unused_693_);
v___x_624_ = v_toConstantVal_612_;
v_isShared_625_ = v_isSharedCheck_692_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_levelParams_622_);
lean_inc(v_name_621_);
lean_dec(v_toConstantVal_612_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_692_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_lhs_629_; lean_object* v___x_630_; 
v___x_626_ = lean_box(0);
lean_inc(v_levelParams_622_);
v___x_627_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_622_, v___x_626_);
v___x_628_ = l_Lean_mkConst(v_name_621_, v___x_627_);
v_lhs_629_ = l_Lean_mkAppN(v___x_628_, v_xs_614_);
lean_inc_ref(v_lhs_629_);
v___x_630_ = l_Lean_Meta_mkEq(v_lhs_629_, v_body_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; uint8_t v___x_632_; uint8_t v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref(v___x_630_);
v___x_632_ = 0;
v___x_633_ = 1;
v___x_634_ = 1;
v___x_635_ = l_Lean_Meta_mkForallFVars(v_xs_614_, v_a_631_, v___x_632_, v___x_633_, v___x_633_, v___x_634_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
v___x_637_ = l_Lean_Meta_letToHave(v_a_636_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref(v___x_637_);
v___x_639_ = l_Lean_Meta_mkEqRefl(v_lhs_629_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = l_Lean_Meta_mkLambdaFVars(v_xs_614_, v_a_640_, v___x_632_, v___x_633_, v___x_632_, v___x_633_, v___x_634_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref(v___x_641_);
lean_inc(v_name_613_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v_a_638_);
lean_ctor_set(v___x_624_, 0, v_name_613_);
v___x_644_ = v___x_624_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_name_613_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_levelParams_622_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_a_638_);
v___x_644_ = v_reuseFailAlloc_651_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_a_648_; lean_object* v___x_649_; 
lean_inc(v_name_613_);
v___x_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_645_, 0, v_name_613_);
lean_ctor_set(v___x_645_, 1, v___x_626_);
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v_a_642_);
lean_ctor_set(v___x_646_, 2, v___x_645_);
v___x_647_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_646_, v___y_619_);
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
v___x_649_ = l_Lean_addDecl(v_a_648_, v___x_632_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v___x_649_);
v___x_650_ = l_Lean_inferDefEqAttr(v_name_613_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
return v___x_650_;
}
else
{
lean_dec(v_name_613_);
return v___x_649_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_638_);
lean_del_object(v___x_624_);
lean_dec(v_levelParams_622_);
lean_dec(v_name_613_);
v_a_652_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_641_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_641_);
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
lean_dec(v_a_638_);
lean_del_object(v___x_624_);
lean_dec(v_levelParams_622_);
lean_dec(v_name_613_);
v_a_660_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_639_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_639_);
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
lean_dec_ref(v_lhs_629_);
lean_del_object(v___x_624_);
lean_dec(v_levelParams_622_);
lean_dec(v_name_613_);
v_a_668_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_637_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_637_);
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
lean_dec_ref(v_lhs_629_);
lean_del_object(v___x_624_);
lean_dec(v_levelParams_622_);
lean_dec(v_name_613_);
v_a_676_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_635_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_635_);
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
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v_lhs_629_);
lean_del_object(v___x_624_);
lean_dec(v_levelParams_622_);
lean_dec(v_name_613_);
v_a_684_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_630_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_630_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_694_, lean_object* v_name_695_, lean_object* v_xs_696_, lean_object* v_body_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_694_, v_name_695_, v_xs_696_, v_body_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_xs_696_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_704_, lean_object* v_info_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_toConstantVal_711_; lean_object* v_value_712_; lean_object* v___f_713_; uint8_t v___x_714_; lean_object* v___x_715_; 
v_toConstantVal_711_ = lean_ctor_get(v_info_705_, 0);
lean_inc_ref(v_toConstantVal_711_);
v_value_712_ = lean_ctor_get(v_info_705_, 1);
lean_inc_ref(v_value_712_);
lean_dec_ref(v_info_705_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_713_, 0, v_toConstantVal_711_);
lean_closure_set(v___f_713_, 1, v_name_704_);
v___x_714_ = 1;
v___x_715_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_712_, v___f_713_, v___x_714_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_716_, lean_object* v_info_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_716_, v_info_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_724_, lean_object* v_name_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_734_; lean_object* v_env_735_; uint8_t v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_st_ref_get(v_a_729_);
v_env_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_env_735_);
lean_dec(v___x_734_);
v___x_736_ = 0;
lean_inc(v_declName_724_);
v___x_737_ = l_Lean_Environment_find_x3f(v_env_735_, v_declName_724_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 1)
{
lean_object* v_val_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_764_; 
v_val_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_764_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_764_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_val_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_764_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_val_738_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_val_742_ = lean_ctor_get(v_val_738_, 0);
lean_inc_ref(v_val_742_);
lean_dec_ref(v_val_738_);
lean_inc_n(v_name_725_, 2);
v___x_743_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_743_, 0, v_name_725_);
lean_closure_set(v___x_743_, 1, v_val_742_);
v___x_744_ = l_Lean_Meta_realizeConst(v_declName_724_, v_name_725_, v___x_743_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_754_; 
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_744_, 0);
lean_dec(v_unused_755_);
v___x_746_ = v___x_744_;
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
else
{
lean_dec(v___x_744_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v_name_725_);
v___x_749_ = v___x_740_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_name_725_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_749_);
v___x_751_ = v___x_746_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_del_object(v___x_740_);
lean_dec(v_name_725_);
v_a_756_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_744_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_744_);
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
else
{
lean_del_object(v___x_740_);
lean_dec(v_val_738_);
lean_dec(v_name_725_);
lean_dec(v_declName_724_);
goto v___jp_731_;
}
}
}
else
{
lean_dec(v___x_737_);
lean_dec(v_name_725_);
lean_dec(v_declName_724_);
goto v___jp_731_;
}
v___jp_731_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_765_, lean_object* v_name_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Meta_mkSimpleEqThm(v_declName_765_, v_name_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_773_, lean_object* v_vals_774_, lean_object* v_i_775_, lean_object* v_k_776_){
_start:
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = lean_array_get_size(v_keys_773_);
v___x_778_ = lean_nat_dec_lt(v_i_775_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v_i_775_);
v___x_779_ = lean_box(0);
return v___x_779_;
}
else
{
lean_object* v_k_x27_780_; uint8_t v___x_781_; 
v_k_x27_780_ = lean_array_fget_borrowed(v_keys_773_, v_i_775_);
v___x_781_ = lean_name_eq(v_k_776_, v_k_x27_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_nat_add(v_i_775_, v___x_782_);
lean_dec(v_i_775_);
v_i_775_ = v___x_783_;
goto _start;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_array_fget_borrowed(v_vals_774_, v_i_775_);
lean_dec(v_i_775_);
lean_inc(v___x_785_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_787_, lean_object* v_vals_788_, lean_object* v_i_789_, lean_object* v_k_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_787_, v_vals_788_, v_i_789_, v_k_790_);
lean_dec(v_k_790_);
lean_dec_ref(v_vals_788_);
lean_dec_ref(v_keys_787_);
return v_res_791_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; 
v___x_792_ = ((size_t)5ULL);
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_shift_left(v___x_793_, v___x_792_);
return v___x_794_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; 
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_797_ = lean_usize_sub(v___x_796_, v___x_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_798_, size_t v_x_799_, lean_object* v_x_800_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v_es_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_822_; 
v_es_801_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_822_ == 0)
{
v___x_803_ = v_x_798_;
v_isShared_804_ = v_isSharedCheck_822_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_es_801_);
lean_dec(v_x_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_822_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; size_t v___x_806_; size_t v___x_807_; size_t v___x_808_; lean_object* v_j_809_; lean_object* v___x_810_; 
v___x_805_ = lean_box(2);
v___x_806_ = ((size_t)5ULL);
v___x_807_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_808_ = lean_usize_land(v_x_799_, v___x_807_);
v_j_809_ = lean_usize_to_nat(v___x_808_);
v___x_810_ = lean_array_get(v___x_805_, v_es_801_, v_j_809_);
lean_dec(v_j_809_);
lean_dec_ref(v_es_801_);
switch(lean_obj_tag(v___x_810_))
{
case 0:
{
lean_object* v_key_811_; lean_object* v_val_812_; uint8_t v___x_813_; 
v_key_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_key_811_);
v_val_812_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_val_812_);
lean_dec_ref(v___x_810_);
v___x_813_ = lean_name_eq(v_x_800_, v_key_811_);
lean_dec(v_key_811_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
lean_dec(v_val_812_);
lean_del_object(v___x_803_);
v___x_814_ = lean_box(0);
return v___x_814_;
}
else
{
lean_object* v___x_816_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 1);
lean_ctor_set(v___x_803_, 0, v_val_812_);
v___x_816_ = v___x_803_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_val_812_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
case 1:
{
lean_object* v_node_818_; size_t v___x_819_; 
lean_del_object(v___x_803_);
v_node_818_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_node_818_);
lean_dec_ref(v___x_810_);
v___x_819_ = lean_usize_shift_right(v_x_799_, v___x_806_);
v_x_798_ = v_node_818_;
v_x_799_ = v___x_819_;
goto _start;
}
default: 
{
lean_object* v___x_821_; 
lean_del_object(v___x_803_);
v___x_821_ = lean_box(0);
return v___x_821_;
}
}
}
}
else
{
lean_object* v_ks_823_; lean_object* v_vs_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_ks_823_ = lean_ctor_get(v_x_798_, 0);
lean_inc_ref(v_ks_823_);
v_vs_824_ = lean_ctor_get(v_x_798_, 1);
lean_inc_ref(v_vs_824_);
lean_dec_ref(v_x_798_);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_823_, v_vs_824_, v___x_825_, v_x_800_);
lean_dec_ref(v_vs_824_);
lean_dec_ref(v_ks_823_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
size_t v_x_355__boxed_830_; lean_object* v_res_831_; 
v_x_355__boxed_830_ = lean_unbox_usize(v_x_828_);
lean_dec(v_x_828_);
v_res_831_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_827_, v_x_355__boxed_830_, v_x_829_);
lean_dec(v_x_829_);
return v_res_831_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_832_; uint64_t v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(1723u);
v___x_833_ = lean_uint64_of_nat(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
uint64_t v___y_837_; 
if (lean_obj_tag(v_x_835_) == 0)
{
uint64_t v___x_840_; 
v___x_840_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_837_ = v___x_840_;
goto v___jp_836_;
}
else
{
uint64_t v_hash_841_; 
v_hash_841_ = lean_ctor_get_uint64(v_x_835_, sizeof(void*)*2);
v___y_837_ = v_hash_841_;
goto v___jp_836_;
}
v___jp_836_:
{
size_t v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_uint64_to_usize(v___y_837_);
v___x_839_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_834_, v___x_838_, v_x_835_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_842_, v_x_843_);
lean_dec(v_x_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; lean_object* v_env_849_; lean_object* v___x_850_; lean_object* v_asyncMode_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_848_ = lean_st_ref_get(v_a_846_);
v_env_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc_ref(v_env_849_);
lean_dec(v___x_848_);
v___x_850_ = l_Lean_Meta_eqnsExt;
v_asyncMode_851_ = lean_ctor_get(v___x_850_, 2);
v___x_852_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_853_ = lean_box(0);
v___x_854_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_852_, v___x_850_, v_env_849_, v_asyncMode_851_, v___x_853_);
v___x_855_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_854_, v_thmName_845_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec(v_thmName_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_861_, v_a_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_866_, v_a_867_, v_a_868_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_thmName_866_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_875_, v_x_876_, v_x_877_);
lean_dec(v_x_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, size_t v_x_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_880_, v_x_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
size_t v_x_472__boxed_888_; lean_object* v_res_889_; 
v_x_472__boxed_888_ = lean_unbox_usize(v_x_886_);
lean_dec(v_x_886_);
v_res_889_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_884_, v_x_885_, v_x_472__boxed_888_, v_x_887_);
lean_dec(v_x_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_890_, lean_object* v_keys_891_, lean_object* v_vals_892_, lean_object* v_heq_893_, lean_object* v_i_894_, lean_object* v_k_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_891_, v_vals_892_, v_i_894_, v_k_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_897_, lean_object* v_keys_898_, lean_object* v_vals_899_, lean_object* v_heq_900_, lean_object* v_i_901_, lean_object* v_k_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_897_, v_keys_898_, v_vals_899_, v_heq_900_, v_i_901_, v_k_902_);
lean_dec(v_k_902_);
lean_dec_ref(v_vals_899_);
lean_dec_ref(v_keys_898_);
return v_res_903_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_904_, lean_object* v_i_905_, lean_object* v_k_906_){
_start:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_array_get_size(v_keys_904_);
v___x_908_ = lean_nat_dec_lt(v_i_905_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec(v_i_905_);
return v___x_908_;
}
else
{
lean_object* v_k_x27_909_; uint8_t v___x_910_; 
v_k_x27_909_ = lean_array_fget_borrowed(v_keys_904_, v_i_905_);
v___x_910_ = lean_name_eq(v_k_906_, v_k_x27_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_i_905_, v___x_911_);
lean_dec(v_i_905_);
v_i_905_ = v___x_912_;
goto _start;
}
else
{
lean_dec(v_i_905_);
return v___x_910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_914_, lean_object* v_i_915_, lean_object* v_k_916_){
_start:
{
uint8_t v_res_917_; lean_object* v_r_918_; 
v_res_917_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_914_, v_i_915_, v_k_916_);
lean_dec(v_k_916_);
lean_dec_ref(v_keys_914_);
v_r_918_ = lean_box(v_res_917_);
return v_r_918_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_919_, size_t v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_object* v_es_922_; lean_object* v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v_j_927_; lean_object* v___x_928_; 
v_es_922_ = lean_ctor_get(v_x_919_, 0);
v___x_923_ = lean_box(2);
v___x_924_ = ((size_t)5ULL);
v___x_925_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_926_ = lean_usize_land(v_x_920_, v___x_925_);
v_j_927_ = lean_usize_to_nat(v___x_926_);
v___x_928_ = lean_array_get_borrowed(v___x_923_, v_es_922_, v_j_927_);
lean_dec(v_j_927_);
switch(lean_obj_tag(v___x_928_))
{
case 0:
{
lean_object* v_key_929_; uint8_t v___x_930_; 
v_key_929_ = lean_ctor_get(v___x_928_, 0);
v___x_930_ = lean_name_eq(v_x_921_, v_key_929_);
return v___x_930_;
}
case 1:
{
lean_object* v_node_931_; size_t v___x_932_; 
v_node_931_ = lean_ctor_get(v___x_928_, 0);
v___x_932_ = lean_usize_shift_right(v_x_920_, v___x_924_);
v_x_919_ = v_node_931_;
v_x_920_ = v___x_932_;
goto _start;
}
default: 
{
uint8_t v___x_934_; 
v___x_934_ = 0;
return v___x_934_;
}
}
}
else
{
lean_object* v_ks_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_ks_935_ = lean_ctor_get(v_x_919_, 0);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_935_, v___x_936_, v_x_921_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
size_t v_x_335__boxed_941_; uint8_t v_res_942_; lean_object* v_r_943_; 
v_x_335__boxed_941_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_res_942_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_938_, v_x_335__boxed_941_, v_x_940_);
lean_dec(v_x_940_);
lean_dec_ref(v_x_938_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint64_t v___y_947_; 
if (lean_obj_tag(v_x_945_) == 0)
{
uint64_t v___x_950_; 
v___x_950_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_947_ = v___x_950_;
goto v___jp_946_;
}
else
{
uint64_t v_hash_951_; 
v_hash_951_ = lean_ctor_get_uint64(v_x_945_, sizeof(void*)*2);
v___y_947_ = v_hash_951_;
goto v___jp_946_;
}
v___jp_946_:
{
size_t v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_uint64_to_usize(v___y_947_);
v___x_949_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_944_, v___x_948_, v_x_945_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_952_, v_x_953_);
lean_dec(v_x_953_);
lean_dec_ref(v_x_952_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_env_960_; lean_object* v___x_961_; lean_object* v_asyncMode_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_959_ = lean_st_ref_get(v_a_957_);
v_env_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_env_960_);
lean_dec(v___x_959_);
v___x_961_ = l_Lean_Meta_eqnsExt;
v_asyncMode_962_ = lean_ctor_get(v___x_961_, 2);
v___x_963_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_964_ = lean_box(0);
v___x_965_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_963_, v___x_961_, v_env_960_, v_asyncMode_962_, v___x_964_);
v___x_966_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_965_, v_thmName_956_);
lean_dec(v___x_965_);
v___x_967_ = lean_box(v___x_966_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec(v_thmName_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_973_, v_a_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_isEqnThm(v_thmName_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_thmName_978_);
return v_res_982_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_984_, v_x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
uint8_t v_res_990_; lean_object* v_r_991_; 
v_res_990_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_987_, v_x_988_, v_x_989_);
lean_dec(v_x_989_);
lean_dec_ref(v_x_988_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, size_t v_x_994_, lean_object* v_x_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_993_, v_x_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
size_t v_x_429__boxed_1001_; uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_x_429__boxed_1001_ = lean_unbox_usize(v_x_999_);
lean_dec(v_x_999_);
v_res_1002_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_997_, v_x_998_, v_x_429__boxed_1001_, v_x_1000_);
lean_dec(v_x_1000_);
lean_dec_ref(v_x_998_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1004_, lean_object* v_keys_1005_, lean_object* v_vals_1006_, lean_object* v_heq_1007_, lean_object* v_i_1008_, lean_object* v_k_1009_){
_start:
{
uint8_t v___x_1010_; 
v___x_1010_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1005_, v_i_1008_, v_k_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1011_, lean_object* v_keys_1012_, lean_object* v_vals_1013_, lean_object* v_heq_1014_, lean_object* v_i_1015_, lean_object* v_k_1016_){
_start:
{
uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1011_, v_keys_1012_, v_vals_1013_, v_heq_1014_, v_i_1015_, v_k_1016_);
lean_dec(v_k_1016_);
lean_dec_ref(v_vals_1013_);
lean_dec_ref(v_keys_1012_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v_ks_1023_; lean_object* v_vs_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1048_; 
v_ks_1023_ = lean_ctor_get(v_x_1019_, 0);
v_vs_1024_ = lean_ctor_get(v_x_1019_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1026_ = v_x_1019_;
v_isShared_1027_ = v_isSharedCheck_1048_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_vs_1024_);
lean_inc(v_ks_1023_);
lean_dec(v_x_1019_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1048_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_array_get_size(v_ks_1023_);
v___x_1029_ = lean_nat_dec_lt(v_x_1020_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec(v_x_1020_);
v___x_1030_ = lean_array_push(v_ks_1023_, v_x_1021_);
v___x_1031_ = lean_array_push(v_vs_1024_, v_x_1022_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v___x_1031_);
lean_ctor_set(v___x_1026_, 0, v___x_1030_);
v___x_1033_ = v___x_1026_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
else
{
lean_object* v_k_x27_1035_; uint8_t v___x_1036_; 
v_k_x27_1035_ = lean_array_fget_borrowed(v_ks_1023_, v_x_1020_);
v___x_1036_ = lean_name_eq(v_x_1021_, v_k_x27_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1038_; 
if (v_isShared_1027_ == 0)
{
v___x_1038_ = v___x_1026_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_ks_1023_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_vs_1024_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_x_1020_, v___x_1039_);
lean_dec(v_x_1020_);
v_x_1019_ = v___x_1038_;
v_x_1020_ = v___x_1040_;
goto _start;
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1043_ = lean_array_fset(v_ks_1023_, v_x_1020_, v_x_1021_);
v___x_1044_ = lean_array_fset(v_vs_1024_, v_x_1020_, v_x_1022_);
lean_dec(v_x_1020_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v___x_1044_);
lean_ctor_set(v___x_1026_, 0, v___x_1043_);
v___x_1046_ = v___x_1026_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1049_, lean_object* v_k_1050_, lean_object* v_v_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1049_, v___x_1052_, v_k_1050_, v_v_1051_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1055_, size_t v_x_1056_, size_t v_x_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
lean_object* v_es_1060_; size_t v___x_1061_; size_t v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; lean_object* v_j_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_es_1060_ = lean_ctor_get(v_x_1055_, 0);
v___x_1061_ = ((size_t)5ULL);
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1064_ = lean_usize_land(v_x_1056_, v___x_1063_);
v_j_1065_ = lean_usize_to_nat(v___x_1064_);
v___x_1066_ = lean_array_get_size(v_es_1060_);
v___x_1067_ = lean_nat_dec_lt(v_j_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec(v_j_1065_);
lean_dec(v_x_1059_);
lean_dec(v_x_1058_);
return v_x_1055_;
}
else
{
lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1104_; 
lean_inc_ref(v_es_1060_);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_x_1055_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v_x_1055_, 0);
lean_dec(v_unused_1105_);
v___x_1069_ = v_x_1055_;
v_isShared_1070_ = v_isSharedCheck_1104_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v_x_1055_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1104_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v_v_1071_; lean_object* v___x_1072_; lean_object* v_xs_x27_1073_; lean_object* v___y_1075_; 
v_v_1071_ = lean_array_fget(v_es_1060_, v_j_1065_);
v___x_1072_ = lean_box(0);
v_xs_x27_1073_ = lean_array_fset(v_es_1060_, v_j_1065_, v___x_1072_);
switch(lean_obj_tag(v_v_1071_))
{
case 0:
{
lean_object* v_key_1080_; lean_object* v_val_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1091_; 
v_key_1080_ = lean_ctor_get(v_v_1071_, 0);
v_val_1081_ = lean_ctor_get(v_v_1071_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_v_1071_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1083_ = v_v_1071_;
v_isShared_1084_ = v_isSharedCheck_1091_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_val_1081_);
lean_inc(v_key_1080_);
lean_dec(v_v_1071_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1091_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_name_eq(v_x_1058_, v_key_1080_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_del_object(v___x_1083_);
v___x_1086_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1080_, v_val_1081_, v_x_1058_, v_x_1059_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
v___y_1075_ = v___x_1087_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1089_; 
lean_dec(v_val_1081_);
lean_dec(v_key_1080_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v_x_1059_);
lean_ctor_set(v___x_1083_, 0, v_x_1058_);
v___x_1089_ = v___x_1083_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_x_1058_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_x_1059_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
v___y_1075_ = v___x_1089_;
goto v___jp_1074_;
}
}
}
}
case 1:
{
lean_object* v_node_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1102_; 
v_node_1092_ = lean_ctor_get(v_v_1071_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_v_1071_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1094_ = v_v_1071_;
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_node_1092_);
lean_dec(v_v_1071_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1096_ = lean_usize_shift_right(v_x_1056_, v___x_1061_);
v___x_1097_ = lean_usize_add(v_x_1057_, v___x_1062_);
v___x_1098_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1092_, v___x_1096_, v___x_1097_, v_x_1058_, v_x_1059_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1098_);
v___x_1100_ = v___x_1094_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v___y_1075_ = v___x_1100_;
goto v___jp_1074_;
}
}
}
default: 
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_x_1058_);
lean_ctor_set(v___x_1103_, 1, v_x_1059_);
v___y_1075_ = v___x_1103_;
goto v___jp_1074_;
}
}
v___jp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_array_fset(v_xs_x27_1073_, v_j_1065_, v___y_1075_);
lean_dec(v_j_1065_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1076_);
v___x_1078_ = v___x_1069_;
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
}
}
}
else
{
lean_object* v_ks_1106_; lean_object* v_vs_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1127_; 
v_ks_1106_ = lean_ctor_get(v_x_1055_, 0);
v_vs_1107_ = lean_ctor_get(v_x_1055_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_x_1055_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1109_ = v_x_1055_;
v_isShared_1110_ = v_isSharedCheck_1127_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_vs_1107_);
lean_inc(v_ks_1106_);
lean_dec(v_x_1055_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1127_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_ks_1106_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_vs_1107_);
v___x_1112_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v_newNode_1113_; uint8_t v___y_1115_; size_t v___x_1121_; uint8_t v___x_1122_; 
v_newNode_1113_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1112_, v_x_1058_, v_x_1059_);
v___x_1121_ = ((size_t)7ULL);
v___x_1122_ = lean_usize_dec_le(v___x_1121_, v_x_1057_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1113_);
v___x_1124_ = lean_unsigned_to_nat(4u);
v___x_1125_ = lean_nat_dec_lt(v___x_1123_, v___x_1124_);
lean_dec(v___x_1123_);
v___y_1115_ = v___x_1125_;
goto v___jp_1114_;
}
else
{
v___y_1115_ = v___x_1122_;
goto v___jp_1114_;
}
v___jp_1114_:
{
if (v___y_1115_ == 0)
{
lean_object* v_ks_1116_; lean_object* v_vs_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_ks_1116_ = lean_ctor_get(v_newNode_1113_, 0);
lean_inc_ref(v_ks_1116_);
v_vs_1117_ = lean_ctor_get(v_newNode_1113_, 1);
lean_inc_ref(v_vs_1117_);
lean_dec_ref(v_newNode_1113_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1120_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1057_, v_ks_1116_, v_vs_1117_, v___x_1118_, v___x_1119_);
lean_dec_ref(v_vs_1117_);
lean_dec_ref(v_ks_1116_);
return v___x_1120_;
}
else
{
return v_newNode_1113_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1128_, lean_object* v_keys_1129_, lean_object* v_vals_1130_, lean_object* v_i_1131_, lean_object* v_entries_1132_){
_start:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_array_get_size(v_keys_1129_);
v___x_1134_ = lean_nat_dec_lt(v_i_1131_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec(v_i_1131_);
return v_entries_1132_;
}
else
{
lean_object* v_k_1135_; lean_object* v_v_1136_; uint64_t v___y_1138_; 
v_k_1135_ = lean_array_fget_borrowed(v_keys_1129_, v_i_1131_);
v_v_1136_ = lean_array_fget_borrowed(v_vals_1130_, v_i_1131_);
if (lean_obj_tag(v_k_1135_) == 0)
{
uint64_t v___x_1149_; 
v___x_1149_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1138_ = v___x_1149_;
goto v___jp_1137_;
}
else
{
uint64_t v_hash_1150_; 
v_hash_1150_ = lean_ctor_get_uint64(v_k_1135_, sizeof(void*)*2);
v___y_1138_ = v_hash_1150_;
goto v___jp_1137_;
}
v___jp_1137_:
{
size_t v_h_1139_; size_t v___x_1140_; lean_object* v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; size_t v_h_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_h_1139_ = lean_uint64_to_usize(v___y_1138_);
v___x_1140_ = ((size_t)5ULL);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = ((size_t)1ULL);
v___x_1143_ = lean_usize_sub(v_depth_1128_, v___x_1142_);
v___x_1144_ = lean_usize_mul(v___x_1140_, v___x_1143_);
v_h_1145_ = lean_usize_shift_right(v_h_1139_, v___x_1144_);
v___x_1146_ = lean_nat_add(v_i_1131_, v___x_1141_);
lean_dec(v_i_1131_);
lean_inc(v_v_1136_);
lean_inc(v_k_1135_);
v___x_1147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1132_, v_h_1145_, v_depth_1128_, v_k_1135_, v_v_1136_);
v_i_1131_ = v___x_1146_;
v_entries_1132_ = v___x_1147_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1151_, lean_object* v_keys_1152_, lean_object* v_vals_1153_, lean_object* v_i_1154_, lean_object* v_entries_1155_){
_start:
{
size_t v_depth_boxed_1156_; lean_object* v_res_1157_; 
v_depth_boxed_1156_ = lean_unbox_usize(v_depth_1151_);
lean_dec(v_depth_1151_);
v_res_1157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1156_, v_keys_1152_, v_vals_1153_, v_i_1154_, v_entries_1155_);
lean_dec_ref(v_vals_1153_);
lean_dec_ref(v_keys_1152_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
size_t v_x_634__boxed_1163_; size_t v_x_635__boxed_1164_; lean_object* v_res_1165_; 
v_x_634__boxed_1163_ = lean_unbox_usize(v_x_1159_);
lean_dec(v_x_1159_);
v_x_635__boxed_1164_ = lean_unbox_usize(v_x_1160_);
lean_dec(v_x_1160_);
v_res_1165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1158_, v_x_634__boxed_1163_, v_x_635__boxed_1164_, v_x_1161_, v_x_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v_x_1168_){
_start:
{
uint64_t v___y_1170_; 
if (lean_obj_tag(v_x_1167_) == 0)
{
uint64_t v___x_1174_; 
v___x_1174_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1170_ = v___x_1174_;
goto v___jp_1169_;
}
else
{
uint64_t v_hash_1175_; 
v_hash_1175_ = lean_ctor_get_uint64(v_x_1167_, sizeof(void*)*2);
v___y_1170_ = v_hash_1175_;
goto v___jp_1169_;
}
v___jp_1169_:
{
size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = lean_uint64_to_usize(v___y_1170_);
v___x_1172_ = ((size_t)1ULL);
v___x_1173_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1166_, v___x_1171_, v___x_1172_, v_x_1167_, v_x_1168_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1176_, lean_object* v_as_1177_, size_t v_i_1178_, size_t v_stop_1179_, lean_object* v_b_1180_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_eq(v_i_1178_, v_stop_1179_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; 
v___x_1182_ = lean_array_uget_borrowed(v_as_1177_, v_i_1178_);
lean_inc(v_declName_1176_);
lean_inc(v___x_1182_);
v___x_1183_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1180_, v___x_1182_, v_declName_1176_);
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = lean_usize_add(v_i_1178_, v___x_1184_);
v_i_1178_ = v___x_1185_;
v_b_1180_ = v___x_1183_;
goto _start;
}
else
{
lean_dec(v_declName_1176_);
return v_b_1180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1187_, lean_object* v_as_1188_, lean_object* v_i_1189_, lean_object* v_stop_1190_, lean_object* v_b_1191_){
_start:
{
size_t v_i_boxed_1192_; size_t v_stop_boxed_1193_; lean_object* v_res_1194_; 
v_i_boxed_1192_ = lean_unbox_usize(v_i_1189_);
lean_dec(v_i_1189_);
v_stop_boxed_1193_ = lean_unbox_usize(v_stop_1190_);
lean_dec(v_stop_1190_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1187_, v_as_1188_, v_i_boxed_1192_, v_stop_boxed_1193_, v_b_1191_);
lean_dec_ref(v_as_1188_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1195_, lean_object* v_declName_1196_, lean_object* v_s_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get_size(v_eqThms_1195_);
v___x_1200_ = lean_nat_dec_lt(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec(v_declName_1196_);
return v_s_1197_;
}
else
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_nat_dec_le(v___x_1199_, v___x_1199_);
if (v___x_1201_ == 0)
{
if (v___x_1200_ == 0)
{
lean_dec(v_declName_1196_);
return v_s_1197_;
}
else
{
size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = ((size_t)0ULL);
v___x_1203_ = lean_usize_of_nat(v___x_1199_);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1196_, v_eqThms_1195_, v___x_1202_, v___x_1203_, v_s_1197_);
return v___x_1204_;
}
}
else
{
size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((size_t)0ULL);
v___x_1206_ = lean_usize_of_nat(v___x_1199_);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1196_, v_eqThms_1195_, v___x_1205_, v___x_1206_, v_s_1197_);
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1208_, lean_object* v_declName_1209_, lean_object* v_s_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1208_, v_declName_1209_, v_s_1210_);
lean_dec_ref(v_eqThms_1208_);
return v_res_1211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0(void){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1217_, lean_object* v_eqThms_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v_env_1222_; lean_object* v_nextMacroScope_1223_; lean_object* v_ngen_1224_; lean_object* v_auxDeclNGen_1225_; lean_object* v_traceState_1226_; lean_object* v_messages_1227_; lean_object* v_infoState_1228_; lean_object* v_snapshotTasks_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1245_; 
v___x_1221_ = lean_st_ref_take(v_a_1219_);
v_env_1222_ = lean_ctor_get(v___x_1221_, 0);
v_nextMacroScope_1223_ = lean_ctor_get(v___x_1221_, 1);
v_ngen_1224_ = lean_ctor_get(v___x_1221_, 2);
v_auxDeclNGen_1225_ = lean_ctor_get(v___x_1221_, 3);
v_traceState_1226_ = lean_ctor_get(v___x_1221_, 4);
v_messages_1227_ = lean_ctor_get(v___x_1221_, 6);
v_infoState_1228_ = lean_ctor_get(v___x_1221_, 7);
v_snapshotTasks_1229_ = lean_ctor_get(v___x_1221_, 8);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1221_, 5);
lean_dec(v_unused_1246_);
v___x_1231_ = v___x_1221_;
v_isShared_1232_ = v_isSharedCheck_1245_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_snapshotTasks_1229_);
lean_inc(v_infoState_1228_);
lean_inc(v_messages_1227_);
lean_inc(v_traceState_1226_);
lean_inc(v_auxDeclNGen_1225_);
lean_inc(v_ngen_1224_);
lean_inc(v_nextMacroScope_1223_);
lean_inc(v_env_1222_);
lean_dec(v___x_1221_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1245_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v_asyncMode_1234_; lean_object* v___f_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1233_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1234_ = lean_ctor_get(v___x_1233_, 2);
v___f_1235_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1235_, 0, v_eqThms_1218_);
lean_closure_set(v___f_1235_, 1, v_declName_1217_);
v___x_1236_ = lean_box(0);
v___x_1237_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1233_, v_env_1222_, v___f_1235_, v_asyncMode_1234_, v___x_1236_);
v___x_1238_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 5, v___x_1238_);
lean_ctor_set(v___x_1231_, 0, v___x_1237_);
v___x_1240_ = v___x_1231_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_nextMacroScope_1223_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_ngen_1224_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_auxDeclNGen_1225_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_traceState_1226_);
lean_ctor_set(v_reuseFailAlloc_1244_, 5, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1244_, 6, v_messages_1227_);
lean_ctor_set(v_reuseFailAlloc_1244_, 7, v_infoState_1228_);
lean_ctor_set(v_reuseFailAlloc_1244_, 8, v_snapshotTasks_1229_);
v___x_1240_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_st_ref_set(v_a_1219_, v___x_1240_);
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1247_, lean_object* v_eqThms_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1247_, v_eqThms_1248_, v_a_1249_);
lean_dec(v_a_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1252_, lean_object* v_eqThms_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1252_, v_eqThms_1253_, v_a_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1258_, lean_object* v_eqThms_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1258_, v_eqThms_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1265_, v_x_1266_, v_x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1269_, lean_object* v_x_1270_, size_t v_x_1271_, size_t v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1270_, v_x_1271_, v_x_1272_, v_x_1273_, v_x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
size_t v_x_912__boxed_1282_; size_t v_x_913__boxed_1283_; lean_object* v_res_1284_; 
v_x_912__boxed_1282_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_x_913__boxed_1283_ = lean_unbox_usize(v_x_1279_);
lean_dec(v_x_1279_);
v_res_1284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1276_, v_x_1277_, v_x_912__boxed_1282_, v_x_913__boxed_1283_, v_x_1280_, v_x_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1285_, lean_object* v_n_1286_, lean_object* v_k_1287_, lean_object* v_v_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1286_, v_k_1287_, v_v_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1290_, size_t v_depth_1291_, lean_object* v_keys_1292_, lean_object* v_vals_1293_, lean_object* v_heq_1294_, lean_object* v_i_1295_, lean_object* v_entries_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1291_, v_keys_1292_, v_vals_1293_, v_i_1295_, v_entries_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1298_, lean_object* v_depth_1299_, lean_object* v_keys_1300_, lean_object* v_vals_1301_, lean_object* v_heq_1302_, lean_object* v_i_1303_, lean_object* v_entries_1304_){
_start:
{
size_t v_depth_boxed_1305_; lean_object* v_res_1306_; 
v_depth_boxed_1305_ = lean_unbox_usize(v_depth_1299_);
lean_dec(v_depth_1299_);
v_res_1306_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1298_, v_depth_boxed_1305_, v_keys_1300_, v_vals_1301_, v_heq_1302_, v_i_1303_, v_entries_1304_);
lean_dec_ref(v_vals_1301_);
lean_dec_ref(v_keys_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1308_, v_x_1309_, v_x_1310_, v_x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1313_, lean_object* v_env_1314_, lean_object* v_idx_1315_, lean_object* v_eqs_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v_nextEq_1323_; uint8_t v___x_1324_; 
v___x_1318_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_nat_add(v_idx_1315_, v___x_1319_);
lean_dec(v_idx_1315_);
lean_inc(v___x_1320_);
v___x_1321_ = l_Nat_reprFast(v___x_1320_);
v___x_1322_ = lean_string_append(v___x_1318_, v___x_1321_);
lean_dec_ref(v___x_1321_);
lean_inc(v_declName_1313_);
lean_inc_ref(v_env_1314_);
v_nextEq_1323_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1314_, v_declName_1313_, v___x_1322_);
v___x_1324_ = l_Lean_Environment_containsOnBranch(v_env_1314_, v_nextEq_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec(v_nextEq_1323_);
lean_dec(v___x_1320_);
lean_dec_ref(v_env_1314_);
lean_dec(v_declName_1313_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_eqs_1316_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_array_push(v_eqs_1316_, v_nextEq_1323_);
v_idx_1315_ = v___x_1320_;
v_eqs_1316_ = v___x_1326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1328_, lean_object* v_env_1329_, lean_object* v_idx_1330_, lean_object* v_eqs_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1328_, v_env_1329_, v_idx_1330_, v_eqs_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1334_, lean_object* v_env_1335_, lean_object* v_idx_1336_, lean_object* v_eqs_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1334_, v_env_1335_, v_idx_1336_, v_eqs_1337_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1344_, lean_object* v_env_1345_, lean_object* v_idx_1346_, lean_object* v_eqs_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1344_, v_env_1345_, v_idx_1346_, v_eqs_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1357_; lean_object* v_env_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; uint8_t v___x_1362_; 
v___x_1357_ = lean_st_ref_get(v_a_1355_);
v_env_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc_ref_n(v_env_1358_, 3);
lean_dec(v___x_1357_);
v___x_1359_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1354_);
v___x_1360_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1358_, v_declName_1354_, v___x_1359_);
v___x_1361_ = 1;
lean_inc(v___x_1360_);
v___x_1362_ = l_Lean_Environment_contains(v_env_1358_, v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v___x_1360_);
lean_dec_ref(v_env_1358_);
lean_dec(v_declName_1354_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_mk_empty_array_with_capacity(v___x_1365_);
v___x_1367_ = lean_array_push(v___x_1366_, v___x_1360_);
lean_inc(v_declName_1354_);
v___x_1368_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1354_, v_env_1358_, v___x_1365_, v___x_1367_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc_n(v_a_1369_, 2);
lean_dec_ref(v___x_1368_);
v___x_1370_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1354_, v_a_1369_, v_a_1355_);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1379_);
v___x_1372_ = v___x_1370_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v___x_1370_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1369_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_declName_1354_);
v_a_1380_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1368_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1368_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1388_, v_a_1389_);
lean_dec(v_a_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1392_, v_a_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1406_, lean_object* v_localInsts_1407_, lean_object* v_x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1406_, v_localInsts_1407_, v_x_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
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
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
v_a_1423_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1414_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1414_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1431_, lean_object* v_localInsts_1432_, lean_object* v_x_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1431_, v_localInsts_1432_, v_x_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1440_, lean_object* v_lctx_1441_, lean_object* v_localInsts_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1441_, v_localInsts_1442_, v_x_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_lctx_1451_, lean_object* v_localInsts_1452_, lean_object* v_x_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1450_, v_lctx_1451_, v_localInsts_1452_, v_x_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1463_, lean_object* v_as_x27_1464_, lean_object* v_b_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
if (lean_obj_tag(v_as_x27_1464_) == 0)
{
lean_object* v___x_1471_; 
lean_dec(v_declName_1463_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_b_1465_);
return v___x_1471_;
}
else
{
lean_object* v_head_1472_; lean_object* v_tail_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v_b_1465_);
v_head_1472_ = lean_ctor_get(v_as_x27_1464_, 0);
v_tail_1473_ = lean_ctor_get(v_as_x27_1464_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_as_x27_1464_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1475_ = v_as_x27_1464_;
v_isShared_1476_ = v_isSharedCheck_1504_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_tail_1473_);
lean_inc(v_head_1472_);
lean_dec(v_as_x27_1464_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1504_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; 
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v_declName_1463_);
v___x_1477_ = lean_apply_6(v_head_1472_, v_declName_1463_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, lean_box(0));
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
v___x_1479_ = lean_box(0);
if (lean_obj_tag(v_a_1478_) == 1)
{
lean_object* v_val_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_tail_1473_);
v_val_1480_ = lean_ctor_get(v_a_1478_, 0);
lean_inc(v_val_1480_);
v___x_1481_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1463_, v_val_1480_, v___y_1469_);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v___x_1481_, 0);
lean_dec(v_unused_1493_);
v___x_1483_ = v___x_1481_;
v_isShared_1484_ = v_isSharedCheck_1492_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v___x_1481_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1492_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_a_1478_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set_tag(v___x_1475_, 0);
lean_ctor_set(v___x_1475_, 1, v___x_1479_);
lean_ctor_set(v___x_1475_, 0, v___x_1485_);
v___x_1487_ = v___x_1475_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1479_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1487_);
v___x_1489_ = v___x_1483_;
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
else
{
lean_object* v___x_1494_; 
lean_dec(v_a_1478_);
lean_del_object(v___x_1475_);
v___x_1494_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1464_ = v_tail_1473_;
v_b_1465_ = v___x_1494_;
goto _start;
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_del_object(v___x_1475_);
lean_dec(v_tail_1473_);
lean_dec(v_declName_1463_);
v_a_1496_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1477_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1477_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1505_, lean_object* v_as_x27_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1505_, v_as_x27_1506_, v_b_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
lean_inc(v_declName_1514_);
v___x_1520_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1558_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1558_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1558_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
uint8_t v___x_1525_; 
v___x_1525_ = lean_unbox(v_a_1521_);
lean_dec(v_a_1521_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_dec(v_declName_1514_);
v___x_1526_ = lean_box(0);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1526_);
v___x_1528_ = v___x_1523_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
else
{
lean_object* v___x_1530_; 
lean_del_object(v___x_1523_);
lean_inc(v_declName_1514_);
v___x_1530_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1514_, v___y_1518_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
if (lean_obj_tag(v_a_1531_) == 1)
{
lean_dec_ref(v_a_1531_);
lean_dec(v_declName_1514_);
return v___x_1530_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_a_1531_);
lean_dec_ref(v___x_1530_);
v___x_1532_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1533_ = lean_st_ref_get(v___x_1532_);
v___x_1534_ = lean_box(0);
v___x_1535_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1536_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1514_, v___x_1533_, v___x_1535_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1549_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1549_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1549_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_fst_1541_; 
v_fst_1541_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_fst_1541_);
lean_dec(v_a_1537_);
if (lean_obj_tag(v_fst_1541_) == 0)
{
lean_object* v___x_1543_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1534_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1534_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
lean_object* v_val_1545_; lean_object* v___x_1547_; 
v_val_1545_ = lean_ctor_get(v_fst_1541_, 0);
lean_inc(v_val_1545_);
lean_dec_ref(v_fst_1541_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v_val_1545_);
v___x_1547_ = v___x_1539_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_val_1545_);
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
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1536_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1536_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_dec(v_declName_1514_);
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_declName_1514_);
v_a_1559_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1520_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1520_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1574_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1577_ = lean_box(1);
v___x_1578_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1579_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v___x_1578_);
lean_ctor_set(v___x_1580_, 2, v___x_1577_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___f_1589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1589_, 0, v_declName_1583_);
v___x_1590_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1591_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1592_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1590_, v___x_1591_, v___f_1589_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1600_, lean_object* v_as_1601_, lean_object* v_as_x27_1602_, lean_object* v_b_1603_, lean_object* v_a_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1600_, v_as_x27_1602_, v_b_1603_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1611_, lean_object* v_as_1612_, lean_object* v_as_x27_1613_, lean_object* v_b_1614_, lean_object* v_a_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1611_, v_as_1612_, v_as_x27_1613_, v_b_1614_, v_a_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v_as_1612_);
return v_res_1621_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(lean_object* v_opts_1622_, lean_object* v_opt_1623_){
_start:
{
lean_object* v_name_1624_; lean_object* v_defValue_1625_; lean_object* v_map_1626_; lean_object* v___x_1627_; 
v_name_1624_ = lean_ctor_get(v_opt_1623_, 0);
v_defValue_1625_ = lean_ctor_get(v_opt_1623_, 1);
v_map_1626_ = lean_ctor_get(v_opts_1622_, 0);
v___x_1627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1626_, v_name_1624_);
if (lean_obj_tag(v___x_1627_) == 0)
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_unbox(v_defValue_1625_);
return v___x_1628_;
}
else
{
lean_object* v_val_1629_; 
v_val_1629_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_val_1629_);
lean_dec_ref(v___x_1627_);
if (lean_obj_tag(v_val_1629_) == 1)
{
uint8_t v_v_1630_; 
v_v_1630_ = lean_ctor_get_uint8(v_val_1629_, 0);
lean_dec_ref(v_val_1629_);
return v_v_1630_;
}
else
{
uint8_t v___x_1631_; 
lean_dec(v_val_1629_);
v___x_1631_ = lean_unbox(v_defValue_1625_);
return v___x_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1___boxed(lean_object* v_opts_1632_, lean_object* v_opt_1633_){
_start:
{
uint8_t v_res_1634_; lean_object* v_r_1635_; 
v_res_1634_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_1632_, v_opt_1633_);
lean_dec_ref(v_opt_1633_);
lean_dec_ref(v_opts_1632_);
v_r_1635_ = lean_box(v_res_1634_);
return v_r_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(lean_object* v_opts_1636_, lean_object* v_opt_1637_){
_start:
{
lean_object* v_name_1638_; lean_object* v_defValue_1639_; lean_object* v_map_1640_; lean_object* v___x_1641_; 
v_name_1638_ = lean_ctor_get(v_opt_1637_, 0);
v_defValue_1639_ = lean_ctor_get(v_opt_1637_, 1);
v_map_1640_ = lean_ctor_get(v_opts_1636_, 0);
v___x_1641_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1640_, v_name_1638_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_inc(v_defValue_1639_);
return v_defValue_1639_;
}
else
{
lean_object* v_val_1642_; 
v_val_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_val_1642_);
lean_dec_ref(v___x_1641_);
if (lean_obj_tag(v_val_1642_) == 3)
{
lean_object* v_v_1643_; 
v_v_1643_ = lean_ctor_get(v_val_1642_, 0);
lean_inc(v_v_1643_);
lean_dec_ref(v_val_1642_);
return v_v_1643_;
}
else
{
lean_dec(v_val_1642_);
lean_inc(v_defValue_1639_);
return v_defValue_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2___boxed(lean_object* v_opts_1644_, lean_object* v_opt_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_1644_, v_opt_1645_);
lean_dec_ref(v_opt_1645_);
lean_dec_ref(v_opts_1644_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(lean_object* v_o_1650_, lean_object* v_k_1651_, uint8_t v_v_1652_){
_start:
{
lean_object* v_map_1653_; uint8_t v_hasTrace_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1668_; 
v_map_1653_ = lean_ctor_get(v_o_1650_, 0);
v_hasTrace_1654_ = lean_ctor_get_uint8(v_o_1650_, sizeof(void*)*1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_o_1650_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1656_ = v_o_1650_;
v_isShared_1657_ = v_isSharedCheck_1668_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_map_1653_);
lean_dec(v_o_1650_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1668_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1658_, 0, v_v_1652_);
lean_inc(v_k_1651_);
v___x_1659_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1651_, v___x_1658_, v_map_1653_);
if (v_hasTrace_1654_ == 0)
{
lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1663_; 
v___x_1660_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1661_ = l_Lean_Name_isPrefixOf(v___x_1660_, v_k_1651_);
lean_dec(v_k_1651_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1659_);
v___x_1663_ = v___x_1656_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1659_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*1, v___x_1661_);
return v___x_1663_;
}
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_k_1651_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1659_);
v___x_1666_ = v___x_1656_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1659_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*1, v_hasTrace_1654_);
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
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___boxed(lean_object* v_o_1669_, lean_object* v_k_1670_, lean_object* v_v_1671_){
_start:
{
uint8_t v_v_boxed_1672_; lean_object* v_res_1673_; 
v_v_boxed_1672_ = lean_unbox(v_v_1671_);
v_res_1673_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_o_1669_, v_k_1670_, v_v_boxed_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(lean_object* v_opts_1674_, lean_object* v_opt_1675_, uint8_t v_val_1676_){
_start:
{
lean_object* v_name_1677_; lean_object* v___x_1678_; 
v_name_1677_ = lean_ctor_get(v_opt_1675_, 0);
lean_inc(v_name_1677_);
lean_dec_ref(v_opt_1675_);
v___x_1678_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_opts_1674_, v_name_1677_, v_val_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object* v_opts_1679_, lean_object* v_opt_1680_, lean_object* v_val_1681_){
_start:
{
uint8_t v_val_boxed_1682_; lean_object* v_res_1683_; 
v_val_boxed_1682_ = lean_unbox(v_val_1681_);
v_res_1683_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_opts_1679_, v_opt_1680_, v_val_boxed_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(lean_object* v_as_1684_, size_t v_i_1685_, size_t v_stop_1686_, lean_object* v_b_1687_){
_start:
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_eq(v_i_1685_, v_stop_1686_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v_defValue_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; 
v___x_1689_ = lean_array_uget_borrowed(v_as_1684_, v_i_1685_);
v_defValue_1690_ = lean_ctor_get(v___x_1689_, 1);
v___x_1691_ = lean_unbox(v_defValue_1690_);
lean_inc(v___x_1689_);
v___x_1692_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_b_1687_, v___x_1689_, v___x_1691_);
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = lean_usize_add(v_i_1685_, v___x_1693_);
v_i_1685_ = v___x_1694_;
v_b_1687_ = v___x_1692_;
goto _start;
}
else
{
return v_b_1687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3___boxed(lean_object* v_as_1696_, lean_object* v_i_1697_, lean_object* v_stop_1698_, lean_object* v_b_1699_){
_start:
{
size_t v_i_boxed_1700_; size_t v_stop_boxed_1701_; lean_object* v_res_1702_; 
v_i_boxed_1700_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_stop_boxed_1701_ = lean_unbox_usize(v_stop_1698_);
lean_dec(v_stop_1698_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v_as_1696_, v_i_boxed_1700_, v_stop_boxed_1701_, v_b_1699_);
lean_dec_ref(v_as_1696_);
return v_res_1702_;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1704_ = lean_array_get_size(v___x_1703_);
return v___x_1704_;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1706_ = lean_nat_dec_le(v___x_1705_, v___x_1705_);
return v___x_1706_;
}
}
static size_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1707_; size_t v___x_1708_; 
v___x_1707_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1708_ = lean_usize_of_nat(v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object* v_declName_1709_, lean_object* v___x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___y_1717_; uint8_t v___y_1718_; lean_object* v_fileName_1719_; lean_object* v_fileMap_1720_; lean_object* v_currRecDepth_1721_; lean_object* v_ref_1722_; lean_object* v_currNamespace_1723_; lean_object* v_openDecls_1724_; lean_object* v_initHeartbeats_1725_; lean_object* v_maxHeartbeats_1726_; lean_object* v_quotContext_1727_; lean_object* v_currMacroScope_1728_; lean_object* v_cancelTk_x3f_1729_; uint8_t v_suppressElabErrors_1730_; lean_object* v_inheritedTraceOptions_1731_; lean_object* v___y_1732_; lean_object* v___x_1737_; lean_object* v_fileName_1738_; lean_object* v_fileMap_1739_; lean_object* v_options_1740_; lean_object* v_currRecDepth_1741_; lean_object* v_ref_1742_; lean_object* v_currNamespace_1743_; lean_object* v_openDecls_1744_; lean_object* v_initHeartbeats_1745_; lean_object* v_maxHeartbeats_1746_; lean_object* v_quotContext_1747_; lean_object* v_currMacroScope_1748_; lean_object* v_cancelTk_x3f_1749_; uint8_t v_suppressElabErrors_1750_; lean_object* v_inheritedTraceOptions_1751_; lean_object* v___y_1753_; uint8_t v___y_1754_; uint8_t v___y_1755_; lean_object* v___y_1777_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1737_ = lean_st_ref_get(v___y_1714_);
v_fileName_1738_ = lean_ctor_get(v___y_1713_, 0);
v_fileMap_1739_ = lean_ctor_get(v___y_1713_, 1);
v_options_1740_ = lean_ctor_get(v___y_1713_, 2);
v_currRecDepth_1741_ = lean_ctor_get(v___y_1713_, 3);
v_ref_1742_ = lean_ctor_get(v___y_1713_, 5);
v_currNamespace_1743_ = lean_ctor_get(v___y_1713_, 6);
v_openDecls_1744_ = lean_ctor_get(v___y_1713_, 7);
v_initHeartbeats_1745_ = lean_ctor_get(v___y_1713_, 8);
v_maxHeartbeats_1746_ = lean_ctor_get(v___y_1713_, 9);
v_quotContext_1747_ = lean_ctor_get(v___y_1713_, 10);
v_currMacroScope_1748_ = lean_ctor_get(v___y_1713_, 11);
v_cancelTk_x3f_1749_ = lean_ctor_get(v___y_1713_, 12);
v_suppressElabErrors_1750_ = lean_ctor_get_uint8(v___y_1713_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1751_ = lean_ctor_get(v___y_1713_, 13);
v___x_1782_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1783_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1784_ = lean_nat_dec_lt(v___x_1710_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_inc_ref(v_options_1740_);
v___y_1777_ = v_options_1740_;
goto v___jp_1776_;
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_uint8_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1);
if (v___x_1785_ == 0)
{
if (v___x_1784_ == 0)
{
lean_inc_ref(v_options_1740_);
v___y_1777_ = v_options_1740_;
goto v___jp_1776_;
}
else
{
size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = ((size_t)0ULL);
v___x_1787_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
lean_inc_ref(v_options_1740_);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1782_, v___x_1786_, v___x_1787_, v_options_1740_);
v___y_1777_ = v___x_1788_;
goto v___jp_1776_;
}
}
else
{
size_t v___x_1789_; size_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((size_t)0ULL);
v___x_1790_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
lean_inc_ref(v_options_1740_);
v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1782_, v___x_1789_, v___x_1790_, v_options_1740_);
v___y_1777_ = v___x_1791_;
goto v___jp_1776_;
}
}
v___jp_1716_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1733_ = l_Lean_maxRecDepth;
v___x_1734_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v___y_1717_, v___x_1733_);
lean_inc_ref(v_inheritedTraceOptions_1731_);
lean_inc(v_cancelTk_x3f_1729_);
lean_inc(v_currMacroScope_1728_);
lean_inc(v_quotContext_1727_);
lean_inc(v_maxHeartbeats_1726_);
lean_inc(v_initHeartbeats_1725_);
lean_inc(v_openDecls_1724_);
lean_inc(v_currNamespace_1723_);
lean_inc(v_ref_1722_);
lean_inc(v_currRecDepth_1721_);
lean_inc_ref(v_fileMap_1720_);
lean_inc_ref(v_fileName_1719_);
v___x_1735_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1735_, 0, v_fileName_1719_);
lean_ctor_set(v___x_1735_, 1, v_fileMap_1720_);
lean_ctor_set(v___x_1735_, 2, v___y_1717_);
lean_ctor_set(v___x_1735_, 3, v_currRecDepth_1721_);
lean_ctor_set(v___x_1735_, 4, v___x_1734_);
lean_ctor_set(v___x_1735_, 5, v_ref_1722_);
lean_ctor_set(v___x_1735_, 6, v_currNamespace_1723_);
lean_ctor_set(v___x_1735_, 7, v_openDecls_1724_);
lean_ctor_set(v___x_1735_, 8, v_initHeartbeats_1725_);
lean_ctor_set(v___x_1735_, 9, v_maxHeartbeats_1726_);
lean_ctor_set(v___x_1735_, 10, v_quotContext_1727_);
lean_ctor_set(v___x_1735_, 11, v_currMacroScope_1728_);
lean_ctor_set(v___x_1735_, 12, v_cancelTk_x3f_1729_);
lean_ctor_set(v___x_1735_, 13, v_inheritedTraceOptions_1731_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*14, v___y_1718_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*14 + 1, v_suppressElabErrors_1730_);
v___x_1736_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1709_, v___y_1711_, v___y_1712_, v___x_1735_, v___y_1732_);
lean_dec_ref(v___x_1735_);
return v___x_1736_;
}
v___jp_1752_:
{
if (v___y_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v_env_1757_; lean_object* v_nextMacroScope_1758_; lean_object* v_ngen_1759_; lean_object* v_auxDeclNGen_1760_; lean_object* v_traceState_1761_; lean_object* v_messages_1762_; lean_object* v_infoState_1763_; lean_object* v_snapshotTasks_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1774_; 
v___x_1756_ = lean_st_ref_take(v___y_1714_);
v_env_1757_ = lean_ctor_get(v___x_1756_, 0);
v_nextMacroScope_1758_ = lean_ctor_get(v___x_1756_, 1);
v_ngen_1759_ = lean_ctor_get(v___x_1756_, 2);
v_auxDeclNGen_1760_ = lean_ctor_get(v___x_1756_, 3);
v_traceState_1761_ = lean_ctor_get(v___x_1756_, 4);
v_messages_1762_ = lean_ctor_get(v___x_1756_, 6);
v_infoState_1763_ = lean_ctor_get(v___x_1756_, 7);
v_snapshotTasks_1764_ = lean_ctor_get(v___x_1756_, 8);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v___x_1756_, 5);
lean_dec(v_unused_1775_);
v___x_1766_ = v___x_1756_;
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snapshotTasks_1764_);
lean_inc(v_infoState_1763_);
lean_inc(v_messages_1762_);
lean_inc(v_traceState_1761_);
lean_inc(v_auxDeclNGen_1760_);
lean_inc(v_ngen_1759_);
lean_inc(v_nextMacroScope_1758_);
lean_inc(v_env_1757_);
lean_dec(v___x_1756_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1768_ = l_Lean_Kernel_enableDiag(v_env_1757_, v___y_1754_);
v___x_1769_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 5, v___x_1769_);
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1771_ = v___x_1766_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_nextMacroScope_1758_);
lean_ctor_set(v_reuseFailAlloc_1773_, 2, v_ngen_1759_);
lean_ctor_set(v_reuseFailAlloc_1773_, 3, v_auxDeclNGen_1760_);
lean_ctor_set(v_reuseFailAlloc_1773_, 4, v_traceState_1761_);
lean_ctor_set(v_reuseFailAlloc_1773_, 5, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1773_, 6, v_messages_1762_);
lean_ctor_set(v_reuseFailAlloc_1773_, 7, v_infoState_1763_);
lean_ctor_set(v_reuseFailAlloc_1773_, 8, v_snapshotTasks_1764_);
v___x_1771_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_st_ref_set(v___y_1714_, v___x_1771_);
v___y_1717_ = v___y_1753_;
v___y_1718_ = v___y_1754_;
v_fileName_1719_ = v_fileName_1738_;
v_fileMap_1720_ = v_fileMap_1739_;
v_currRecDepth_1721_ = v_currRecDepth_1741_;
v_ref_1722_ = v_ref_1742_;
v_currNamespace_1723_ = v_currNamespace_1743_;
v_openDecls_1724_ = v_openDecls_1744_;
v_initHeartbeats_1725_ = v_initHeartbeats_1745_;
v_maxHeartbeats_1726_ = v_maxHeartbeats_1746_;
v_quotContext_1727_ = v_quotContext_1747_;
v_currMacroScope_1728_ = v_currMacroScope_1748_;
v_cancelTk_x3f_1729_ = v_cancelTk_x3f_1749_;
v_suppressElabErrors_1730_ = v_suppressElabErrors_1750_;
v_inheritedTraceOptions_1731_ = v_inheritedTraceOptions_1751_;
v___y_1732_ = v___y_1714_;
goto v___jp_1716_;
}
}
}
else
{
v___y_1717_ = v___y_1753_;
v___y_1718_ = v___y_1754_;
v_fileName_1719_ = v_fileName_1738_;
v_fileMap_1720_ = v_fileMap_1739_;
v_currRecDepth_1721_ = v_currRecDepth_1741_;
v_ref_1722_ = v_ref_1742_;
v_currNamespace_1723_ = v_currNamespace_1743_;
v_openDecls_1724_ = v_openDecls_1744_;
v_initHeartbeats_1725_ = v_initHeartbeats_1745_;
v_maxHeartbeats_1726_ = v_maxHeartbeats_1746_;
v_quotContext_1727_ = v_quotContext_1747_;
v_currMacroScope_1728_ = v_currMacroScope_1748_;
v_cancelTk_x3f_1729_ = v_cancelTk_x3f_1749_;
v_suppressElabErrors_1730_ = v_suppressElabErrors_1750_;
v_inheritedTraceOptions_1731_ = v_inheritedTraceOptions_1751_;
v___y_1732_ = v___y_1714_;
goto v___jp_1716_;
}
}
v___jp_1776_:
{
lean_object* v_env_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; uint8_t v___x_1781_; 
v_env_1778_ = lean_ctor_get(v___x_1737_, 0);
lean_inc_ref(v_env_1778_);
lean_dec(v___x_1737_);
v___x_1779_ = l_Lean_diagnostics;
v___x_1780_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___y_1777_, v___x_1779_);
v___x_1781_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1778_);
lean_dec_ref(v_env_1778_);
if (v___x_1781_ == 0)
{
if (v___x_1780_ == 0)
{
v___y_1717_ = v___y_1777_;
v___y_1718_ = v___x_1780_;
v_fileName_1719_ = v_fileName_1738_;
v_fileMap_1720_ = v_fileMap_1739_;
v_currRecDepth_1721_ = v_currRecDepth_1741_;
v_ref_1722_ = v_ref_1742_;
v_currNamespace_1723_ = v_currNamespace_1743_;
v_openDecls_1724_ = v_openDecls_1744_;
v_initHeartbeats_1725_ = v_initHeartbeats_1745_;
v_maxHeartbeats_1726_ = v_maxHeartbeats_1746_;
v_quotContext_1727_ = v_quotContext_1747_;
v_currMacroScope_1728_ = v_currMacroScope_1748_;
v_cancelTk_x3f_1729_ = v_cancelTk_x3f_1749_;
v_suppressElabErrors_1730_ = v_suppressElabErrors_1750_;
v_inheritedTraceOptions_1731_ = v_inheritedTraceOptions_1751_;
v___y_1732_ = v___y_1714_;
goto v___jp_1716_;
}
else
{
v___y_1753_ = v___y_1777_;
v___y_1754_ = v___x_1780_;
v___y_1755_ = v___x_1781_;
goto v___jp_1752_;
}
}
else
{
v___y_1753_ = v___y_1777_;
v___y_1754_ = v___x_1780_;
v___y_1755_ = v___x_1780_;
goto v___jp_1752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object* v_declName_1792_, lean_object* v___x_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Meta_getEqnsFor_x3f___lam__0(v_declName_1792_, v___x_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___x_1793_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___f_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1806_ = lean_unsigned_to_nat(32u);
v___x_1807_ = lean_mk_empty_array_with_capacity(v___x_1806_);
lean_dec_ref(v___x_1807_);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___f_1809_ = lean_alloc_closure((void*)(l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1809_, 0, v_declName_1800_);
lean_closure_set(v___f_1809_, 1, v___x_1808_);
v___x_1810_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1811_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1812_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1810_, v___x_1811_, v___f_1809_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(lean_object* v_msgData_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v_env_1827_; lean_object* v___x_1828_; lean_object* v_mctx_1829_; lean_object* v_lctx_1830_; lean_object* v_options_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1826_ = lean_st_ref_get(v___y_1824_);
v_env_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc_ref(v_env_1827_);
lean_dec(v___x_1826_);
v___x_1828_ = lean_st_ref_get(v___y_1822_);
v_mctx_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc_ref(v_mctx_1829_);
lean_dec(v___x_1828_);
v_lctx_1830_ = lean_ctor_get(v___y_1821_, 2);
v_options_1831_ = lean_ctor_get(v___y_1823_, 2);
lean_inc_ref(v_options_1831_);
lean_inc_ref(v_lctx_1830_);
v___x_1832_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1832_, 0, v_env_1827_);
lean_ctor_set(v___x_1832_, 1, v_mctx_1829_);
lean_ctor_set(v___x_1832_, 2, v_lctx_1830_);
lean_ctor_set(v___x_1832_, 3, v_options_1831_);
v___x_1833_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v_msgData_1820_);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1___boxed(lean_object* v_msgData_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msgData_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1841_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1842_; double v___x_1843_; 
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_float_of_nat(v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(lean_object* v_cls_1847_, lean_object* v_msg_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_ref_1854_; lean_object* v___x_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1900_; 
v_ref_1854_ = lean_ctor_get(v___y_1851_, 5);
v___x_1855_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msg_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1900_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1900_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v_traceState_1861_; lean_object* v_env_1862_; lean_object* v_nextMacroScope_1863_; lean_object* v_ngen_1864_; lean_object* v_auxDeclNGen_1865_; lean_object* v_cache_1866_; lean_object* v_messages_1867_; lean_object* v_infoState_1868_; lean_object* v_snapshotTasks_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1899_; 
v___x_1860_ = lean_st_ref_take(v___y_1852_);
v_traceState_1861_ = lean_ctor_get(v___x_1860_, 4);
v_env_1862_ = lean_ctor_get(v___x_1860_, 0);
v_nextMacroScope_1863_ = lean_ctor_get(v___x_1860_, 1);
v_ngen_1864_ = lean_ctor_get(v___x_1860_, 2);
v_auxDeclNGen_1865_ = lean_ctor_get(v___x_1860_, 3);
v_cache_1866_ = lean_ctor_get(v___x_1860_, 5);
v_messages_1867_ = lean_ctor_get(v___x_1860_, 6);
v_infoState_1868_ = lean_ctor_get(v___x_1860_, 7);
v_snapshotTasks_1869_ = lean_ctor_get(v___x_1860_, 8);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1871_ = v___x_1860_;
v_isShared_1872_ = v_isSharedCheck_1899_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_snapshotTasks_1869_);
lean_inc(v_infoState_1868_);
lean_inc(v_messages_1867_);
lean_inc(v_cache_1866_);
lean_inc(v_traceState_1861_);
lean_inc(v_auxDeclNGen_1865_);
lean_inc(v_ngen_1864_);
lean_inc(v_nextMacroScope_1863_);
lean_inc(v_env_1862_);
lean_dec(v___x_1860_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1899_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
uint64_t v_tid_1873_; lean_object* v_traces_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1898_; 
v_tid_1873_ = lean_ctor_get_uint64(v_traceState_1861_, sizeof(void*)*1);
v_traces_1874_ = lean_ctor_get(v_traceState_1861_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_traceState_1861_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1876_ = v_traceState_1861_;
v_isShared_1877_ = v_isSharedCheck_1898_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_traces_1874_);
lean_dec(v_traceState_1861_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1898_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; double v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1878_ = lean_box(0);
v___x_1879_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0);
v___x_1880_ = 0;
v___x_1881_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1));
v___x_1882_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1882_, 0, v_cls_1847_);
lean_ctor_set(v___x_1882_, 1, v___x_1878_);
lean_ctor_set(v___x_1882_, 2, v___x_1881_);
lean_ctor_set_float(v___x_1882_, sizeof(void*)*3, v___x_1879_);
lean_ctor_set_float(v___x_1882_, sizeof(void*)*3 + 8, v___x_1879_);
lean_ctor_set_uint8(v___x_1882_, sizeof(void*)*3 + 16, v___x_1880_);
v___x_1883_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__2));
v___x_1884_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v_a_1856_);
lean_ctor_set(v___x_1884_, 2, v___x_1883_);
lean_inc(v_ref_1854_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_ref_1854_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_PersistentArray_push___redArg(v_traces_1874_, v___x_1885_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1886_);
v___x_1888_ = v___x_1876_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1886_);
lean_ctor_set_uint64(v_reuseFailAlloc_1897_, sizeof(void*)*1, v_tid_1873_);
v___x_1888_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 4, v___x_1888_);
v___x_1890_ = v___x_1871_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_env_1862_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_nextMacroScope_1863_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_ngen_1864_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_auxDeclNGen_1865_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1896_, 5, v_cache_1866_);
lean_ctor_set(v_reuseFailAlloc_1896_, 6, v_messages_1867_);
lean_ctor_set(v_reuseFailAlloc_1896_, 7, v_infoState_1868_);
lean_ctor_set(v_reuseFailAlloc_1896_, 8, v_snapshotTasks_1869_);
v___x_1890_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1891_ = lean_st_ref_set(v___y_1852_, v___x_1890_);
v___x_1892_ = lean_box(0);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1892_);
v___x_1894_ = v___x_1858_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___boxed(lean_object* v_cls_1901_, lean_object* v_msg_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(v_cls_1901_, v_msg_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(lean_object* v___x_1909_, lean_object* v_as_1910_, size_t v_i_1911_, size_t v_stop_1912_){
_start:
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_usize_dec_eq(v_i_1911_, v_stop_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v_defValue_1915_; uint8_t v___x_1916_; uint8_t v___y_1922_; uint8_t v___x_1923_; 
v___x_1914_ = lean_array_uget_borrowed(v_as_1910_, v_i_1911_);
v_defValue_1915_ = lean_ctor_get(v___x_1914_, 1);
v___x_1916_ = 1;
v___x_1923_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___x_1909_, v___x_1914_);
if (v___x_1923_ == 0)
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_unbox(v_defValue_1915_);
if (v___x_1924_ == 0)
{
goto v___jp_1917_;
}
else
{
v___y_1922_ = v___x_1923_;
goto v___jp_1921_;
}
}
else
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_unbox(v_defValue_1915_);
v___y_1922_ = v___x_1925_;
goto v___jp_1921_;
}
v___jp_1917_:
{
if (v___x_1913_ == 0)
{
size_t v___x_1918_; size_t v___x_1919_; 
v___x_1918_ = ((size_t)1ULL);
v___x_1919_ = lean_usize_add(v_i_1911_, v___x_1918_);
v_i_1911_ = v___x_1919_;
goto _start;
}
else
{
return v___x_1916_;
}
}
v___jp_1921_:
{
if (v___y_1922_ == 0)
{
return v___x_1916_;
}
else
{
goto v___jp_1917_;
}
}
}
else
{
uint8_t v___x_1926_; 
v___x_1926_ = 0;
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object* v___x_1927_, lean_object* v_as_1928_, lean_object* v_i_1929_, lean_object* v_stop_1930_){
_start:
{
size_t v_i_boxed_1931_; size_t v_stop_boxed_1932_; uint8_t v_res_1933_; lean_object* v_r_1934_; 
v_i_boxed_1931_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_stop_boxed_1932_ = lean_unbox_usize(v_stop_1930_);
lean_dec(v_stop_1930_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v___x_1927_, v_as_1928_, v_i_boxed_1931_, v_stop_boxed_1932_);
lean_dec_ref(v_as_1928_);
lean_dec_ref(v___x_1927_);
v_r_1934_ = lean_box(v_res_1933_);
return v_r_1934_;
}
}
static uint8_t _init_l_Lean_Meta_generateEagerEqns___closed__0(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_nat_dec_lt(v___x_1936_, v___x_1935_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__4(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_1945_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1946_ = l_Lean_Name_append(v___x_1945_, v___x_1944_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__6(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__5));
v___x_1949_ = l_Lean_stringToMessageData(v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object* v_declName_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1983_ = lean_uint8_once(&l_Lean_Meta_generateEagerEqns___closed__0, &l_Lean_Meta_generateEagerEqns___closed__0_once, _init_l_Lean_Meta_generateEagerEqns___closed__0);
if (v___x_1983_ == 0)
{
lean_dec(v_declName_1950_);
goto v___jp_1956_;
}
else
{
if (v___x_1983_ == 0)
{
lean_dec(v_declName_1950_);
goto v___jp_1956_;
}
else
{
lean_object* v_options_1984_; lean_object* v_inheritedTraceOptions_1985_; size_t v___x_1986_; size_t v___x_1987_; uint8_t v___x_1988_; 
v_options_1984_ = lean_ctor_get(v_a_1953_, 2);
v_inheritedTraceOptions_1985_ = lean_ctor_get(v_a_1953_, 13);
v___x_1986_ = ((size_t)0ULL);
v___x_1987_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v_options_1984_, v___x_1982_, v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_dec(v_declName_1950_);
goto v___jp_1956_;
}
else
{
uint8_t v_hasTrace_1989_; 
v_hasTrace_1989_ = lean_ctor_get_uint8(v_options_1984_, sizeof(void*)*1);
if (v_hasTrace_1989_ == 0)
{
v___y_1960_ = v_a_1951_;
v___y_1961_ = v_a_1952_;
v___y_1962_ = v_a_1953_;
v___y_1963_ = v_a_1954_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1990_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_1991_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__4, &l_Lean_Meta_generateEagerEqns___closed__4_once, _init_l_Lean_Meta_generateEagerEqns___closed__4);
v___x_1992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1985_, v_options_1984_, v___x_1991_);
if (v___x_1992_ == 0)
{
v___y_1960_ = v_a_1951_;
v___y_1961_ = v_a_1952_;
v___y_1962_ = v_a_1953_;
v___y_1963_ = v_a_1954_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1993_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__6, &l_Lean_Meta_generateEagerEqns___closed__6_once, _init_l_Lean_Meta_generateEagerEqns___closed__6);
lean_inc(v_declName_1950_);
v___x_1994_ = l_Lean_MessageData_ofName(v_declName_1950_);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(v___x_1990_, v___x_1995_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_dec_ref(v___x_1996_);
v___y_1960_ = v_a_1951_;
v___y_1961_ = v_a_1952_;
v___y_1962_ = v_a_1953_;
v___y_1963_ = v_a_1954_;
goto v___jp_1959_;
}
else
{
lean_dec(v_declName_1950_);
return v___x_1996_;
}
}
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
v___jp_1959_:
{
lean_object* v___x_1964_; 
v___x_1964_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1950_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v___x_1964_, 0);
lean_dec(v_unused_1973_);
v___x_1966_ = v___x_1964_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v___x_1964_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_box(0);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1964_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1964_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___boxed(lean_object* v_declName_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Meta_generateEagerEqns(v_declName_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_box(0);
v___x_2006_ = lean_st_mk_ref(v___x_2005_);
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2029_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2029_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2029_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_unbox(v_a_2013_);
lean_dec(v_a_2013_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
lean_dec_ref(v_f_2010_);
v___x_2018_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 1);
lean_ctor_set(v___x_2015_, 0, v___x_2018_);
v___x_2020_ = v___x_2015_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2022_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2023_ = lean_st_ref_take(v___x_2022_);
v___x_2024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2024_, 0, v_f_2010_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_st_ref_set(v___x_2022_, v___x_2024_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2025_);
v___x_2027_ = v___x_2015_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_f_2010_);
v_a_2030_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2012_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2012_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2044_, lean_object* v_as_x27_2045_, lean_object* v_b_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
if (lean_obj_tag(v_as_x27_2045_) == 0)
{
lean_object* v___x_2052_; 
lean_dec(v_declName_2044_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_b_2046_);
return v___x_2052_;
}
else
{
lean_object* v_head_2053_; lean_object* v_tail_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2082_; 
lean_dec_ref(v_b_2046_);
v_head_2053_ = lean_ctor_get(v_as_x27_2045_, 0);
v_tail_2054_ = lean_ctor_get(v_as_x27_2045_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_as_x27_2045_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2056_ = v_as_x27_2045_;
v_isShared_2057_ = v_isSharedCheck_2082_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_tail_2054_);
lean_inc(v_head_2053_);
lean_dec(v_as_x27_2045_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2082_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; 
lean_inc(v___y_2050_);
lean_inc_ref(v___y_2049_);
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
lean_inc(v_declName_2044_);
v___x_2058_ = lean_apply_6(v_head_2053_, v_declName_2044_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, lean_box(0));
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2073_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_box(0);
if (lean_obj_tag(v_a_2059_) == 1)
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v_tail_2054_);
lean_dec(v_declName_2044_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_a_2059_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 0);
lean_ctor_set(v___x_2056_, 1, v___x_2063_);
lean_ctor_set(v___x_2056_, 0, v___x_2064_);
v___x_2066_ = v___x_2056_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2063_);
v___x_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2066_);
v___x_2068_ = v___x_2061_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
lean_object* v___x_2071_; 
lean_del_object(v___x_2061_);
lean_dec(v_a_2059_);
lean_del_object(v___x_2056_);
v___x_2071_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2045_ = v_tail_2054_;
v_b_2046_ = v___x_2071_;
goto _start;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_del_object(v___x_2056_);
lean_dec(v_tail_2054_);
lean_dec(v_declName_2044_);
v_a_2074_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2058_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2058_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2083_, lean_object* v_as_x27_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2083_, v_as_x27_2084_, v_b_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2092_, lean_object* v_declName_2093_, uint8_t v_nonRec_2094_, lean_object* v___x_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2104_; lean_object* v_env_2105_; uint8_t v___x_2106_; uint8_t v___x_2107_; 
v___x_2104_ = lean_st_ref_get(v___y_2099_);
v_env_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc_ref(v_env_2105_);
lean_dec(v___x_2104_);
v___x_2106_ = 1;
lean_inc(v___x_2092_);
v___x_2107_ = l_Lean_Environment_contains(v_env_2105_, v___x_2092_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec(v___x_2092_);
lean_inc(v_declName_2093_);
v___x_2108_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2093_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
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
lean_dec_ref(v___x_2095_);
lean_dec(v_declName_2093_);
goto v___jp_2101_;
}
else
{
lean_object* v___x_2111_; 
lean_inc(v_declName_2093_);
v___x_2111_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2093_, v___y_2099_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; uint8_t v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2111_);
v___x_2113_ = lean_unbox(v_a_2112_);
lean_dec(v_a_2112_);
if (v___x_2113_ == 0)
{
if (v_nonRec_2094_ == 0)
{
lean_dec_ref(v___x_2095_);
lean_dec(v_declName_2093_);
goto v___jp_2101_;
}
else
{
lean_object* v___x_2114_; lean_object* v_env_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = lean_st_ref_get(v___y_2099_);
v_env_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc_ref(v_env_2115_);
lean_dec(v___x_2114_);
lean_inc(v_declName_2093_);
v___x_2116_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2115_, v_declName_2093_, v___x_2095_);
v___x_2117_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2093_, v___x_2116_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
return v___x_2117_;
}
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v___x_2095_);
v___x_2118_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2119_ = lean_st_ref_get(v___x_2118_);
v___x_2120_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2121_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2093_, v___x_2119_, v___x_2120_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2131_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2131_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2131_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_fst_2126_; 
v_fst_2126_ = lean_ctor_get(v_a_2122_, 0);
lean_inc(v_fst_2126_);
lean_dec(v_a_2122_);
if (lean_obj_tag(v_fst_2126_) == 0)
{
lean_del_object(v___x_2124_);
goto v___jp_2101_;
}
else
{
lean_object* v_val_2127_; lean_object* v___x_2129_; 
v_val_2127_ = lean_ctor_get(v_fst_2126_, 0);
lean_inc(v_val_2127_);
lean_dec_ref(v_fst_2126_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_val_2127_);
v___x_2129_ = v___x_2124_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_val_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
v_a_2132_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2121_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2121_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v___x_2095_);
lean_dec(v_declName_2093_);
v_a_2140_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2111_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2111_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v___x_2095_);
lean_dec(v_declName_2093_);
v_a_2148_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2108_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2108_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v___x_2095_);
lean_dec(v_declName_2093_);
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2092_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
v___jp_2101_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2158_, lean_object* v_declName_2159_, lean_object* v_nonRec_2160_, lean_object* v___x_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_nonRec_boxed_2167_; lean_object* v_res_2168_; 
v_nonRec_boxed_2167_ = lean_unbox(v_nonRec_2160_);
v_res_2168_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2158_, v_declName_2159_, v_nonRec_boxed_2167_, v___x_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_ref_2175_; lean_object* v___x_2176_; lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2185_; 
v_ref_2175_ = lean_ctor_get(v___y_2172_, 5);
v___x_2176_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msg_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
lean_inc(v_ref_2175_);
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v_ref_2175_);
lean_ctor_set(v___x_2181_, 1, v_a_2177_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set_tag(v___x_2179_, 1);
lean_ctor_set(v___x_2179_, 0, v___x_2181_);
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2193_, uint8_t v_isExporting_2194_, lean_object* v___x_2195_, lean_object* v___y_2196_, lean_object* v___x_2197_, lean_object* v_a_x3f_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v_env_2201_; lean_object* v_nextMacroScope_2202_; lean_object* v_ngen_2203_; lean_object* v_auxDeclNGen_2204_; lean_object* v_traceState_2205_; lean_object* v_messages_2206_; lean_object* v_infoState_2207_; lean_object* v_snapshotTasks_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2233_; 
v___x_2200_ = lean_st_ref_take(v___y_2193_);
v_env_2201_ = lean_ctor_get(v___x_2200_, 0);
v_nextMacroScope_2202_ = lean_ctor_get(v___x_2200_, 1);
v_ngen_2203_ = lean_ctor_get(v___x_2200_, 2);
v_auxDeclNGen_2204_ = lean_ctor_get(v___x_2200_, 3);
v_traceState_2205_ = lean_ctor_get(v___x_2200_, 4);
v_messages_2206_ = lean_ctor_get(v___x_2200_, 6);
v_infoState_2207_ = lean_ctor_get(v___x_2200_, 7);
v_snapshotTasks_2208_ = lean_ctor_get(v___x_2200_, 8);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; 
v_unused_2234_ = lean_ctor_get(v___x_2200_, 5);
lean_dec(v_unused_2234_);
v___x_2210_ = v___x_2200_;
v_isShared_2211_ = v_isSharedCheck_2233_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_snapshotTasks_2208_);
lean_inc(v_infoState_2207_);
lean_inc(v_messages_2206_);
lean_inc(v_traceState_2205_);
lean_inc(v_auxDeclNGen_2204_);
lean_inc(v_ngen_2203_);
lean_inc(v_nextMacroScope_2202_);
lean_inc(v_env_2201_);
lean_dec(v___x_2200_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2233_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = l_Lean_Environment_setExporting(v_env_2201_, v_isExporting_2194_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 5, v___x_2195_);
lean_ctor_set(v___x_2210_, 0, v___x_2212_);
v___x_2214_ = v___x_2210_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_nextMacroScope_2202_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_ngen_2203_);
lean_ctor_set(v_reuseFailAlloc_2232_, 3, v_auxDeclNGen_2204_);
lean_ctor_set(v_reuseFailAlloc_2232_, 4, v_traceState_2205_);
lean_ctor_set(v_reuseFailAlloc_2232_, 5, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2232_, 6, v_messages_2206_);
lean_ctor_set(v_reuseFailAlloc_2232_, 7, v_infoState_2207_);
lean_ctor_set(v_reuseFailAlloc_2232_, 8, v_snapshotTasks_2208_);
v___x_2214_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v_mctx_2217_; lean_object* v_zetaDeltaFVarIds_2218_; lean_object* v_postponed_2219_; lean_object* v_diag_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2230_; 
v___x_2215_ = lean_st_ref_set(v___y_2193_, v___x_2214_);
v___x_2216_ = lean_st_ref_take(v___y_2196_);
v_mctx_2217_ = lean_ctor_get(v___x_2216_, 0);
v_zetaDeltaFVarIds_2218_ = lean_ctor_get(v___x_2216_, 2);
v_postponed_2219_ = lean_ctor_get(v___x_2216_, 3);
v_diag_2220_ = lean_ctor_get(v___x_2216_, 4);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2216_, 1);
lean_dec(v_unused_2231_);
v___x_2222_ = v___x_2216_;
v_isShared_2223_ = v_isSharedCheck_2230_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_diag_2220_);
lean_inc(v_postponed_2219_);
lean_inc(v_zetaDeltaFVarIds_2218_);
lean_inc(v_mctx_2217_);
lean_dec(v___x_2216_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2230_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v___x_2197_);
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_mctx_2217_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_zetaDeltaFVarIds_2218_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_postponed_2219_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_diag_2220_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = lean_st_ref_set(v___y_2196_, v___x_2225_);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2235_, lean_object* v_isExporting_2236_, lean_object* v___x_2237_, lean_object* v___y_2238_, lean_object* v___x_2239_, lean_object* v_a_x3f_2240_, lean_object* v___y_2241_){
_start:
{
uint8_t v_isExporting_boxed_2242_; lean_object* v_res_2243_; 
v_isExporting_boxed_2242_ = lean_unbox(v_isExporting_2236_);
v_res_2243_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2235_, v_isExporting_boxed_2242_, v___x_2237_, v___y_2238_, v___x_2239_, v_a_x3f_2240_);
lean_dec(v_a_x3f_2240_);
lean_dec(v___y_2238_);
lean_dec(v___y_2235_);
return v_res_2243_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_2245_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
lean_ctor_set(v___x_2245_, 2, v___x_2244_);
lean_ctor_set(v___x_2245_, 3, v___x_2244_);
lean_ctor_set(v___x_2245_, 4, v___x_2244_);
lean_ctor_set(v___x_2245_, 5, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2246_, uint8_t v_isExporting_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v_env_2254_; uint8_t v_isExporting_2255_; lean_object* v___x_2256_; lean_object* v_env_2257_; lean_object* v_nextMacroScope_2258_; lean_object* v_ngen_2259_; lean_object* v_auxDeclNGen_2260_; lean_object* v_traceState_2261_; lean_object* v_messages_2262_; lean_object* v_infoState_2263_; lean_object* v_snapshotTasks_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2318_; 
v___x_2253_ = lean_st_ref_get(v___y_2251_);
v_env_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc_ref(v_env_2254_);
lean_dec(v___x_2253_);
v_isExporting_2255_ = lean_ctor_get_uint8(v_env_2254_, sizeof(void*)*8);
lean_dec_ref(v_env_2254_);
v___x_2256_ = lean_st_ref_take(v___y_2251_);
v_env_2257_ = lean_ctor_get(v___x_2256_, 0);
v_nextMacroScope_2258_ = lean_ctor_get(v___x_2256_, 1);
v_ngen_2259_ = lean_ctor_get(v___x_2256_, 2);
v_auxDeclNGen_2260_ = lean_ctor_get(v___x_2256_, 3);
v_traceState_2261_ = lean_ctor_get(v___x_2256_, 4);
v_messages_2262_ = lean_ctor_get(v___x_2256_, 6);
v_infoState_2263_ = lean_ctor_get(v___x_2256_, 7);
v_snapshotTasks_2264_ = lean_ctor_get(v___x_2256_, 8);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v___x_2256_, 5);
lean_dec(v_unused_2319_);
v___x_2266_ = v___x_2256_;
v_isShared_2267_ = v_isSharedCheck_2318_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_snapshotTasks_2264_);
lean_inc(v_infoState_2263_);
lean_inc(v_messages_2262_);
lean_inc(v_traceState_2261_);
lean_inc(v_auxDeclNGen_2260_);
lean_inc(v_ngen_2259_);
lean_inc(v_nextMacroScope_2258_);
lean_inc(v_env_2257_);
lean_dec(v___x_2256_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2318_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2268_ = l_Lean_Environment_setExporting(v_env_2257_, v_isExporting_2247_);
v___x_2269_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 5, v___x_2269_);
lean_ctor_set(v___x_2266_, 0, v___x_2268_);
v___x_2271_ = v___x_2266_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_nextMacroScope_2258_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_ngen_2259_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_auxDeclNGen_2260_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v_traceState_2261_);
lean_ctor_set(v_reuseFailAlloc_2317_, 5, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2317_, 6, v_messages_2262_);
lean_ctor_set(v_reuseFailAlloc_2317_, 7, v_infoState_2263_);
lean_ctor_set(v_reuseFailAlloc_2317_, 8, v_snapshotTasks_2264_);
v___x_2271_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v_mctx_2274_; lean_object* v_zetaDeltaFVarIds_2275_; lean_object* v_postponed_2276_; lean_object* v_diag_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2315_; 
v___x_2272_ = lean_st_ref_set(v___y_2251_, v___x_2271_);
v___x_2273_ = lean_st_ref_take(v___y_2249_);
v_mctx_2274_ = lean_ctor_get(v___x_2273_, 0);
v_zetaDeltaFVarIds_2275_ = lean_ctor_get(v___x_2273_, 2);
v_postponed_2276_ = lean_ctor_get(v___x_2273_, 3);
v_diag_2277_ = lean_ctor_get(v___x_2273_, 4);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v___x_2273_, 1);
lean_dec(v_unused_2316_);
v___x_2279_ = v___x_2273_;
v_isShared_2280_ = v_isSharedCheck_2315_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_diag_2277_);
lean_inc(v_postponed_2276_);
lean_inc(v_zetaDeltaFVarIds_2275_);
lean_inc(v_mctx_2274_);
lean_dec(v___x_2273_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2315_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2281_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v___x_2281_);
v___x_2283_ = v___x_2279_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_mctx_2274_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_zetaDeltaFVarIds_2275_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_postponed_2276_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_diag_2277_);
v___x_2283_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v_r_2285_; 
v___x_2284_ = lean_st_ref_set(v___y_2249_, v___x_2283_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v___y_2248_);
v_r_2285_ = lean_apply_5(v_x_2246_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, lean_box(0));
if (lean_obj_tag(v_r_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2302_; 
v_a_2286_ = lean_ctor_get(v_r_2285_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_r_2285_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2288_ = v_r_2285_;
v_isShared_2289_ = v_isSharedCheck_2302_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v_r_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2302_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
lean_inc(v_a_2286_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set_tag(v___x_2288_, 1);
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
v___x_2292_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2251_, v_isExporting_2255_, v___x_2269_, v___y_2249_, v___x_2281_, v___x_2291_);
lean_dec_ref(v___x_2291_);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2299_ == 0)
{
lean_object* v_unused_2300_; 
v_unused_2300_ = lean_ctor_get(v___x_2292_, 0);
lean_dec(v_unused_2300_);
v___x_2294_ = v___x_2292_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_dec(v___x_2292_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v_a_2286_);
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2286_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
v_a_2303_ = lean_ctor_get(v_r_2285_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v_r_2285_);
v___x_2304_ = lean_box(0);
v___x_2305_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2251_, v_isExporting_2255_, v___x_2269_, v___y_2249_, v___x_2281_, v___x_2304_);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v___x_2305_, 0);
lean_dec(v_unused_2313_);
v___x_2307_ = v___x_2305_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_dec(v___x_2305_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set_tag(v___x_2307_, 1);
lean_ctor_set(v___x_2307_, 0, v_a_2303_);
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2303_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2320_, lean_object* v_isExporting_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v_isExporting_boxed_2327_; lean_object* v_res_2328_; 
v_isExporting_boxed_2327_ = lean_unbox(v_isExporting_2321_);
v_res_2328_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2320_, v_isExporting_boxed_2327_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2329_, uint8_t v_when_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
if (v_when_2330_ == 0)
{
lean_object* v___x_2336_; 
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
v___x_2336_ = lean_apply_5(v_x_2329_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, lean_box(0));
return v___x_2336_;
}
else
{
uint8_t v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = 0;
v___x_2338_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2329_, v___x_2337_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2339_, lean_object* v_when_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v_when_boxed_2346_; lean_object* v_res_2347_; 
v_when_boxed_2346_ = lean_unbox(v_when_2340_);
v_res_2347_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2339_, v_when_boxed_2346_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2347_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2350_ = l_Lean_stringToMessageData(v___x_2349_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2353_ = l_Lean_stringToMessageData(v___x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2356_ = l_Lean_stringToMessageData(v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2357_, uint8_t v_nonRec_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v_env_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; 
v___x_2364_ = lean_st_ref_get(v___y_2362_);
v_env_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc_ref(v_env_2365_);
lean_dec(v___x_2364_);
v___x_2366_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2357_);
v___x_2367_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2365_, v_declName_2357_, v___x_2366_);
v___x_2368_ = lean_box(v_nonRec_2358_);
lean_inc(v___x_2367_);
v___f_2369_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2369_, 0, v___x_2367_);
lean_closure_set(v___f_2369_, 1, v_declName_2357_);
lean_closure_set(v___f_2369_, 2, v___x_2368_);
lean_closure_set(v___f_2369_, 3, v___x_2366_);
v___x_2370_ = 1;
v___x_2371_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2369_, v___x_2370_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
if (lean_obj_tag(v_a_2372_) == 1)
{
lean_object* v_val_2373_; uint8_t v___x_2374_; 
v_val_2373_ = lean_ctor_get(v_a_2372_, 0);
lean_inc(v_val_2373_);
lean_dec_ref(v_a_2372_);
v___x_2374_ = lean_name_eq(v_val_2373_, v___x_2367_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec_ref(v___x_2371_);
v___x_2375_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2376_ = l_Lean_MessageData_ofName(v_val_2373_);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = l_Lean_MessageData_ofName(v___x_2367_);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2383_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
else
{
lean_dec(v_val_2373_);
lean_dec(v___x_2367_);
return v___x_2371_;
}
}
else
{
lean_dec(v_a_2372_);
lean_dec(v___x_2367_);
return v___x_2371_;
}
}
else
{
lean_dec(v___x_2367_);
return v___x_2371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2393_, lean_object* v_nonRec_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
uint8_t v_nonRec_boxed_2400_; lean_object* v_res_2401_; 
v_nonRec_boxed_2400_ = lean_unbox(v_nonRec_2394_);
v_res_2401_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2393_, v_nonRec_boxed_2400_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2402_, uint8_t v_nonRec_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2409_; lean_object* v___f_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2409_ = lean_box(v_nonRec_2403_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2410_, 0, v_declName_2402_);
lean_closure_set(v___f_2410_, 1, v___x_2409_);
v___x_2411_ = lean_unsigned_to_nat(32u);
v___x_2412_ = lean_mk_empty_array_with_capacity(v___x_2411_);
lean_dec_ref(v___x_2412_);
v___x_2413_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2415_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2413_, v___x_2414_, v___f_2410_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2416_, lean_object* v_nonRec_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
uint8_t v_nonRec_boxed_2423_; lean_object* v_res_2424_; 
v_nonRec_boxed_2423_ = lean_unbox(v_nonRec_2417_);
v_res_2424_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2416_, v_nonRec_boxed_2423_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2425_, lean_object* v_as_2426_, lean_object* v_as_x27_2427_, lean_object* v_b_2428_, lean_object* v_a_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2425_, v_as_x27_2427_, v_b_2428_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2436_, lean_object* v_as_2437_, lean_object* v_as_x27_2438_, lean_object* v_b_2439_, lean_object* v_a_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2436_, v_as_2437_, v_as_x27_2438_, v_b_2439_, v_a_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v_as_2437_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2447_, lean_object* v_x_2448_, uint8_t v_isExporting_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2448_, v_isExporting_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2456_, lean_object* v_x_2457_, lean_object* v_isExporting_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
uint8_t v_isExporting_boxed_2464_; lean_object* v_res_2465_; 
v_isExporting_boxed_2464_ = lean_unbox(v_isExporting_2458_);
v_res_2465_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2456_, v_x_2457_, v_isExporting_boxed_2464_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2466_, lean_object* v_x_2467_, uint8_t v_when_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2467_, v_when_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2475_, lean_object* v_x_2476_, lean_object* v_when_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
uint8_t v_when_boxed_2483_; lean_object* v_res_2484_; 
v_when_boxed_2483_ = lean_unbox(v_when_2477_);
v_res_2484_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2475_, v_x_2476_, v_when_boxed_2483_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2485_, lean_object* v_msg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2493_, lean_object* v_msg_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2493_, v_msg_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2500_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = lean_unsigned_to_nat(32u);
v___x_2502_ = lean_mk_empty_array_with_capacity(v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2504_ = ((size_t)5ULL);
v___x_2505_ = lean_unsigned_to_nat(0u);
v___x_2506_ = lean_unsigned_to_nat(32u);
v___x_2507_ = lean_mk_empty_array_with_capacity(v___x_2506_);
v___x_2508_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2509_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2507_);
lean_ctor_set(v___x_2509_, 2, v___x_2505_);
lean_ctor_set(v___x_2509_, 3, v___x_2505_);
lean_ctor_set_usize(v___x_2509_, 4, v___x_2504_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v_traceState_2513_; lean_object* v_traces_2514_; lean_object* v___x_2515_; lean_object* v_traceState_2516_; lean_object* v_env_2517_; lean_object* v_nextMacroScope_2518_; lean_object* v_ngen_2519_; lean_object* v_auxDeclNGen_2520_; lean_object* v_cache_2521_; lean_object* v_messages_2522_; lean_object* v_infoState_2523_; lean_object* v_snapshotTasks_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2543_; 
v___x_2512_ = lean_st_ref_get(v___y_2510_);
v_traceState_2513_ = lean_ctor_get(v___x_2512_, 4);
lean_inc_ref(v_traceState_2513_);
lean_dec(v___x_2512_);
v_traces_2514_ = lean_ctor_get(v_traceState_2513_, 0);
lean_inc_ref(v_traces_2514_);
lean_dec_ref(v_traceState_2513_);
v___x_2515_ = lean_st_ref_take(v___y_2510_);
v_traceState_2516_ = lean_ctor_get(v___x_2515_, 4);
v_env_2517_ = lean_ctor_get(v___x_2515_, 0);
v_nextMacroScope_2518_ = lean_ctor_get(v___x_2515_, 1);
v_ngen_2519_ = lean_ctor_get(v___x_2515_, 2);
v_auxDeclNGen_2520_ = lean_ctor_get(v___x_2515_, 3);
v_cache_2521_ = lean_ctor_get(v___x_2515_, 5);
v_messages_2522_ = lean_ctor_get(v___x_2515_, 6);
v_infoState_2523_ = lean_ctor_get(v___x_2515_, 7);
v_snapshotTasks_2524_ = lean_ctor_get(v___x_2515_, 8);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2526_ = v___x_2515_;
v_isShared_2527_ = v_isSharedCheck_2543_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_snapshotTasks_2524_);
lean_inc(v_infoState_2523_);
lean_inc(v_messages_2522_);
lean_inc(v_cache_2521_);
lean_inc(v_traceState_2516_);
lean_inc(v_auxDeclNGen_2520_);
lean_inc(v_ngen_2519_);
lean_inc(v_nextMacroScope_2518_);
lean_inc(v_env_2517_);
lean_dec(v___x_2515_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2543_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
uint64_t v_tid_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2541_; 
v_tid_2528_ = lean_ctor_get_uint64(v_traceState_2516_, sizeof(void*)*1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_traceState_2516_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v_traceState_2516_, 0);
lean_dec(v_unused_2542_);
v___x_2530_ = v_traceState_2516_;
v_isShared_2531_ = v_isSharedCheck_2541_;
goto v_resetjp_2529_;
}
else
{
lean_dec(v_traceState_2516_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2541_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2532_);
v___x_2534_ = v___x_2530_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2532_);
lean_ctor_set_uint64(v_reuseFailAlloc_2540_, sizeof(void*)*1, v_tid_2528_);
v___x_2534_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2536_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 4, v___x_2534_);
v___x_2536_ = v___x_2526_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_env_2517_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_nextMacroScope_2518_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_ngen_2519_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_auxDeclNGen_2520_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2539_, 5, v_cache_2521_);
lean_ctor_set(v_reuseFailAlloc_2539_, 6, v_messages_2522_);
lean_ctor_set(v_reuseFailAlloc_2539_, 7, v_infoState_2523_);
lean_ctor_set(v_reuseFailAlloc_2539_, 8, v_snapshotTasks_2524_);
v___x_2536_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_st_ref_set(v___y_2510_, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_traces_2514_);
return v___x_2538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2544_);
lean_dec(v___y_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = 0;
v___x_2560_ = lean_box(v___x_2559_);
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2569_ = l_Lean_stringToMessageData(v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2570_, lean_object* v_x_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2575_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2576_ = l_Lean_MessageData_ofName(v_name_2570_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2579_, lean_object* v_x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2579_, v_x_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_x_2580_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_x_2585_){
_start:
{
if (lean_obj_tag(v_x_2585_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
v_a_2587_ = lean_ctor_get(v_x_2585_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_x_2585_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v_x_2585_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v_x_2585_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 1);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
v_a_2595_ = lean_ctor_get(v_x_2585_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_x_2585_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v_x_2585_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v_x_2585_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 0);
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object* v_x_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_2603_);
return v_res_2605_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_e_2606_){
_start:
{
if (lean_obj_tag(v_e_2606_) == 0)
{
uint8_t v___x_2607_; 
v___x_2607_ = 2;
return v___x_2607_;
}
else
{
lean_object* v_a_2608_; uint8_t v___x_2609_; 
v_a_2608_ = lean_ctor_get(v_e_2606_, 0);
v___x_2609_ = lean_unbox(v_a_2608_);
if (v___x_2609_ == 0)
{
uint8_t v___x_2610_; 
v___x_2610_ = 1;
return v___x_2610_;
}
else
{
uint8_t v___x_2611_; 
v___x_2611_ = 0;
return v___x_2611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_e_2612_){
_start:
{
uint8_t v_res_2613_; lean_object* v_r_2614_; 
v_res_2613_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_e_2612_);
lean_dec_ref(v_e_2612_);
v_r_2614_ = lean_box(v_res_2613_);
return v_r_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(size_t v_sz_2615_, size_t v_i_2616_, lean_object* v_bs_2617_){
_start:
{
uint8_t v___x_2618_; 
v___x_2618_ = lean_usize_dec_lt(v_i_2616_, v_sz_2615_);
if (v___x_2618_ == 0)
{
return v_bs_2617_;
}
else
{
lean_object* v_v_2619_; lean_object* v_msg_2620_; lean_object* v___x_2621_; lean_object* v_bs_x27_2622_; size_t v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
v_v_2619_ = lean_array_uget_borrowed(v_bs_2617_, v_i_2616_);
v_msg_2620_ = lean_ctor_get(v_v_2619_, 1);
lean_inc_ref(v_msg_2620_);
v___x_2621_ = lean_unsigned_to_nat(0u);
v_bs_x27_2622_ = lean_array_uset(v_bs_2617_, v_i_2616_, v___x_2621_);
v___x_2623_ = ((size_t)1ULL);
v___x_2624_ = lean_usize_add(v_i_2616_, v___x_2623_);
v___x_2625_ = lean_array_uset(v_bs_x27_2622_, v_i_2616_, v_msg_2620_);
v_i_2616_ = v___x_2624_;
v_bs_2617_ = v___x_2625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_sz_2627_, lean_object* v_i_2628_, lean_object* v_bs_2629_){
_start:
{
size_t v_sz_boxed_2630_; size_t v_i_boxed_2631_; lean_object* v_res_2632_; 
v_sz_boxed_2630_ = lean_unbox_usize(v_sz_2627_);
lean_dec(v_sz_2627_);
v_i_boxed_2631_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_boxed_2630_, v_i_boxed_2631_, v_bs_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_oldTraces_2633_, lean_object* v_data_2634_, lean_object* v_ref_2635_, lean_object* v_msg_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_fileName_2640_; lean_object* v_fileMap_2641_; lean_object* v_options_2642_; lean_object* v_currRecDepth_2643_; lean_object* v_maxRecDepth_2644_; lean_object* v_ref_2645_; lean_object* v_currNamespace_2646_; lean_object* v_openDecls_2647_; lean_object* v_initHeartbeats_2648_; lean_object* v_maxHeartbeats_2649_; lean_object* v_quotContext_2650_; lean_object* v_currMacroScope_2651_; uint8_t v_diag_2652_; lean_object* v_cancelTk_x3f_2653_; uint8_t v_suppressElabErrors_2654_; lean_object* v_inheritedTraceOptions_2655_; lean_object* v___x_2656_; lean_object* v_traceState_2657_; lean_object* v_traces_2658_; lean_object* v_ref_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; size_t v_sz_2662_; size_t v___x_2663_; lean_object* v___x_2664_; lean_object* v_msg_2665_; lean_object* v___x_2666_; lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2704_; 
v_fileName_2640_ = lean_ctor_get(v___y_2637_, 0);
v_fileMap_2641_ = lean_ctor_get(v___y_2637_, 1);
v_options_2642_ = lean_ctor_get(v___y_2637_, 2);
v_currRecDepth_2643_ = lean_ctor_get(v___y_2637_, 3);
v_maxRecDepth_2644_ = lean_ctor_get(v___y_2637_, 4);
v_ref_2645_ = lean_ctor_get(v___y_2637_, 5);
v_currNamespace_2646_ = lean_ctor_get(v___y_2637_, 6);
v_openDecls_2647_ = lean_ctor_get(v___y_2637_, 7);
v_initHeartbeats_2648_ = lean_ctor_get(v___y_2637_, 8);
v_maxHeartbeats_2649_ = lean_ctor_get(v___y_2637_, 9);
v_quotContext_2650_ = lean_ctor_get(v___y_2637_, 10);
v_currMacroScope_2651_ = lean_ctor_get(v___y_2637_, 11);
v_diag_2652_ = lean_ctor_get_uint8(v___y_2637_, sizeof(void*)*14);
v_cancelTk_x3f_2653_ = lean_ctor_get(v___y_2637_, 12);
v_suppressElabErrors_2654_ = lean_ctor_get_uint8(v___y_2637_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2655_ = lean_ctor_get(v___y_2637_, 13);
v___x_2656_ = lean_st_ref_get(v___y_2638_);
v_traceState_2657_ = lean_ctor_get(v___x_2656_, 4);
lean_inc_ref(v_traceState_2657_);
lean_dec(v___x_2656_);
v_traces_2658_ = lean_ctor_get(v_traceState_2657_, 0);
lean_inc_ref(v_traces_2658_);
lean_dec_ref(v_traceState_2657_);
v_ref_2659_ = l_Lean_replaceRef(v_ref_2635_, v_ref_2645_);
lean_inc_ref(v_inheritedTraceOptions_2655_);
lean_inc(v_cancelTk_x3f_2653_);
lean_inc(v_currMacroScope_2651_);
lean_inc(v_quotContext_2650_);
lean_inc(v_maxHeartbeats_2649_);
lean_inc(v_initHeartbeats_2648_);
lean_inc(v_openDecls_2647_);
lean_inc(v_currNamespace_2646_);
lean_inc(v_maxRecDepth_2644_);
lean_inc(v_currRecDepth_2643_);
lean_inc_ref(v_options_2642_);
lean_inc_ref(v_fileMap_2641_);
lean_inc_ref(v_fileName_2640_);
v___x_2660_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2660_, 0, v_fileName_2640_);
lean_ctor_set(v___x_2660_, 1, v_fileMap_2641_);
lean_ctor_set(v___x_2660_, 2, v_options_2642_);
lean_ctor_set(v___x_2660_, 3, v_currRecDepth_2643_);
lean_ctor_set(v___x_2660_, 4, v_maxRecDepth_2644_);
lean_ctor_set(v___x_2660_, 5, v_ref_2659_);
lean_ctor_set(v___x_2660_, 6, v_currNamespace_2646_);
lean_ctor_set(v___x_2660_, 7, v_openDecls_2647_);
lean_ctor_set(v___x_2660_, 8, v_initHeartbeats_2648_);
lean_ctor_set(v___x_2660_, 9, v_maxHeartbeats_2649_);
lean_ctor_set(v___x_2660_, 10, v_quotContext_2650_);
lean_ctor_set(v___x_2660_, 11, v_currMacroScope_2651_);
lean_ctor_set(v___x_2660_, 12, v_cancelTk_x3f_2653_);
lean_ctor_set(v___x_2660_, 13, v_inheritedTraceOptions_2655_);
lean_ctor_set_uint8(v___x_2660_, sizeof(void*)*14, v_diag_2652_);
lean_ctor_set_uint8(v___x_2660_, sizeof(void*)*14 + 1, v_suppressElabErrors_2654_);
v___x_2661_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2658_);
lean_dec_ref(v_traces_2658_);
v_sz_2662_ = lean_array_size(v___x_2661_);
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_2662_, v___x_2663_, v___x_2661_);
v_msg_2665_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2665_, 0, v_data_2634_);
lean_ctor_set(v_msg_2665_, 1, v_msg_2636_);
lean_ctor_set(v_msg_2665_, 2, v___x_2664_);
v___x_2666_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2665_, v___x_2660_, v___y_2638_);
lean_dec_ref(v___x_2660_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2704_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2704_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v_traceState_2672_; lean_object* v_env_2673_; lean_object* v_nextMacroScope_2674_; lean_object* v_ngen_2675_; lean_object* v_auxDeclNGen_2676_; lean_object* v_cache_2677_; lean_object* v_messages_2678_; lean_object* v_infoState_2679_; lean_object* v_snapshotTasks_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2703_; 
v___x_2671_ = lean_st_ref_take(v___y_2638_);
v_traceState_2672_ = lean_ctor_get(v___x_2671_, 4);
v_env_2673_ = lean_ctor_get(v___x_2671_, 0);
v_nextMacroScope_2674_ = lean_ctor_get(v___x_2671_, 1);
v_ngen_2675_ = lean_ctor_get(v___x_2671_, 2);
v_auxDeclNGen_2676_ = lean_ctor_get(v___x_2671_, 3);
v_cache_2677_ = lean_ctor_get(v___x_2671_, 5);
v_messages_2678_ = lean_ctor_get(v___x_2671_, 6);
v_infoState_2679_ = lean_ctor_get(v___x_2671_, 7);
v_snapshotTasks_2680_ = lean_ctor_get(v___x_2671_, 8);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2682_ = v___x_2671_;
v_isShared_2683_ = v_isSharedCheck_2703_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_snapshotTasks_2680_);
lean_inc(v_infoState_2679_);
lean_inc(v_messages_2678_);
lean_inc(v_cache_2677_);
lean_inc(v_traceState_2672_);
lean_inc(v_auxDeclNGen_2676_);
lean_inc(v_ngen_2675_);
lean_inc(v_nextMacroScope_2674_);
lean_inc(v_env_2673_);
lean_dec(v___x_2671_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2703_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
uint64_t v_tid_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2701_; 
v_tid_2684_ = lean_ctor_get_uint64(v_traceState_2672_, sizeof(void*)*1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_traceState_2672_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v_traceState_2672_, 0);
lean_dec(v_unused_2702_);
v___x_2686_ = v_traceState_2672_;
v_isShared_2687_ = v_isSharedCheck_2701_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v_traceState_2672_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2701_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_ref_2635_);
lean_ctor_set(v___x_2688_, 1, v_a_2667_);
v___x_2689_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2633_, v___x_2688_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2689_);
v___x_2691_ = v___x_2686_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2689_);
lean_ctor_set_uint64(v_reuseFailAlloc_2700_, sizeof(void*)*1, v_tid_2684_);
v___x_2691_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 4, v___x_2691_);
v___x_2693_ = v___x_2682_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_env_2673_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_nextMacroScope_2674_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_ngen_2675_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_auxDeclNGen_2676_);
lean_ctor_set(v_reuseFailAlloc_2699_, 4, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2699_, 5, v_cache_2677_);
lean_ctor_set(v_reuseFailAlloc_2699_, 6, v_messages_2678_);
lean_ctor_set(v_reuseFailAlloc_2699_, 7, v_infoState_2679_);
lean_ctor_set(v_reuseFailAlloc_2699_, 8, v_snapshotTasks_2680_);
v___x_2693_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2694_ = lean_st_ref_set(v___y_2638_, v___x_2693_);
v___x_2695_ = lean_box(0);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2695_);
v___x_2697_ = v___x_2669_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_oldTraces_2705_, lean_object* v_data_2706_, lean_object* v_ref_2707_, lean_object* v_msg_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2705_, v_data_2706_, v_ref_2707_, v_msg_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
return v_res_2712_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2715_ = l_Lean_stringToMessageData(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4(void){
_start:
{
lean_object* v___x_2719_; double v___x_2720_; 
v___x_2719_ = lean_unsigned_to_nat(1000u);
v___x_2720_ = lean_float_of_nat(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2721_, uint8_t v_collapsed_2722_, lean_object* v_tag_2723_, lean_object* v_opts_2724_, uint8_t v_clsEnabled_2725_, lean_object* v_oldTraces_2726_, lean_object* v_msg_2727_, lean_object* v_resStartStop_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_fst_2732_; lean_object* v_snd_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2831_; 
v_fst_2732_ = lean_ctor_get(v_resStartStop_2728_, 0);
v_snd_2733_ = lean_ctor_get(v_resStartStop_2728_, 1);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_resStartStop_2728_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2735_ = v_resStartStop_2728_;
v_isShared_2736_ = v_isSharedCheck_2831_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_snd_2733_);
lean_inc(v_fst_2732_);
lean_dec(v_resStartStop_2728_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2831_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v_data_2740_; lean_object* v_fst_2751_; lean_object* v_snd_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2830_; 
v_fst_2751_ = lean_ctor_get(v_snd_2733_, 0);
v_snd_2752_ = lean_ctor_get(v_snd_2733_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_snd_2733_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2754_ = v_snd_2733_;
v_isShared_2755_ = v_isSharedCheck_2830_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_snd_2752_);
lean_inc(v_fst_2751_);
lean_dec(v_snd_2733_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2830_;
goto v_resetjp_2753_;
}
v___jp_2737_:
{
lean_object* v___x_2741_; 
lean_inc(v___y_2738_);
v___x_2741_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2726_, v_data_2740_, v___y_2738_, v___y_2739_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; 
lean_dec_ref(v___x_2741_);
v___x_2742_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2732_);
return v___x_2742_;
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_fst_2732_);
v_a_2743_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2741_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; uint8_t v___x_2757_; lean_object* v___y_2759_; lean_object* v_a_2760_; uint8_t v___y_2784_; double v___y_2815_; 
v___x_2756_ = l_Lean_trace_profiler;
v___x_2757_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2724_, v___x_2756_);
if (v___x_2757_ == 0)
{
v___y_2784_ = v___x_2757_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2821_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2724_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; double v___x_2824_; double v___x_2825_; double v___x_2826_; 
v___x_2822_ = l_Lean_trace_profiler_threshold;
v___x_2823_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2724_, v___x_2822_);
v___x_2824_ = lean_float_of_nat(v___x_2823_);
v___x_2825_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4);
v___x_2826_ = lean_float_div(v___x_2824_, v___x_2825_);
v___y_2815_ = v___x_2826_;
goto v___jp_2814_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; double v___x_2829_; 
v___x_2827_ = l_Lean_trace_profiler_threshold;
v___x_2828_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2724_, v___x_2827_);
v___x_2829_ = lean_float_of_nat(v___x_2828_);
v___y_2815_ = v___x_2829_;
goto v___jp_2814_;
}
}
v___jp_2758_:
{
uint8_t v_result_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v_result_2761_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_fst_2732_);
v___x_2762_ = l_Lean_TraceResult_toEmoji(v_result_2761_);
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
v___x_2764_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
if (v_isShared_2755_ == 0)
{
lean_ctor_set_tag(v___x_2754_, 7);
lean_ctor_set(v___x_2754_, 1, v___x_2764_);
lean_ctor_set(v___x_2754_, 0, v___x_2763_);
v___x_2766_ = v___x_2754_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2763_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v_m_2768_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set_tag(v___x_2735_, 7);
lean_ctor_set(v___x_2735_, 1, v_a_2760_);
lean_ctor_set(v___x_2735_, 0, v___x_2766_);
v_m_2768_ = v___x_2735_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_a_2760_);
v_m_2768_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; double v___x_2771_; lean_object* v_data_2772_; 
v___x_2769_ = lean_box(v_result_2761_);
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
v___x_2771_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0);
lean_inc_ref(v_tag_2723_);
lean_inc_ref(v___x_2770_);
lean_inc(v_cls_2721_);
v_data_2772_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2772_, 0, v_cls_2721_);
lean_ctor_set(v_data_2772_, 1, v___x_2770_);
lean_ctor_set(v_data_2772_, 2, v_tag_2723_);
lean_ctor_set_float(v_data_2772_, sizeof(void*)*3, v___x_2771_);
lean_ctor_set_float(v_data_2772_, sizeof(void*)*3 + 8, v___x_2771_);
lean_ctor_set_uint8(v_data_2772_, sizeof(void*)*3 + 16, v_collapsed_2722_);
if (v___x_2757_ == 0)
{
lean_dec_ref(v___x_2770_);
lean_dec(v_snd_2752_);
lean_dec(v_fst_2751_);
lean_dec_ref(v_tag_2723_);
lean_dec(v_cls_2721_);
v___y_2738_ = v___y_2759_;
v___y_2739_ = v_m_2768_;
v_data_2740_ = v_data_2772_;
goto v___jp_2737_;
}
else
{
lean_object* v_data_2773_; double v___x_2774_; double v___x_2775_; 
lean_dec_ref(v_data_2772_);
v_data_2773_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2773_, 0, v_cls_2721_);
lean_ctor_set(v_data_2773_, 1, v___x_2770_);
lean_ctor_set(v_data_2773_, 2, v_tag_2723_);
v___x_2774_ = lean_unbox_float(v_fst_2751_);
lean_dec(v_fst_2751_);
lean_ctor_set_float(v_data_2773_, sizeof(void*)*3, v___x_2774_);
v___x_2775_ = lean_unbox_float(v_snd_2752_);
lean_dec(v_snd_2752_);
lean_ctor_set_float(v_data_2773_, sizeof(void*)*3 + 8, v___x_2775_);
lean_ctor_set_uint8(v_data_2773_, sizeof(void*)*3 + 16, v_collapsed_2722_);
v___y_2738_ = v___y_2759_;
v___y_2739_ = v_m_2768_;
v_data_2740_ = v_data_2773_;
goto v___jp_2737_;
}
}
}
}
v___jp_2778_:
{
lean_object* v_ref_2779_; lean_object* v___x_2780_; 
v_ref_2779_ = lean_ctor_get(v___y_2729_, 5);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v_fst_2732_);
v___x_2780_ = lean_apply_4(v_msg_2727_, v_fst_2732_, v___y_2729_, v___y_2730_, lean_box(0));
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref(v___x_2780_);
v___y_2759_ = v_ref_2779_;
v_a_2760_ = v_a_2781_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2782_; 
lean_dec_ref(v___x_2780_);
v___x_2782_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3);
v___y_2759_ = v_ref_2779_;
v_a_2760_ = v___x_2782_;
goto v___jp_2758_;
}
}
v___jp_2783_:
{
if (v_clsEnabled_2725_ == 0)
{
if (v___y_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v_traceState_2786_; lean_object* v_env_2787_; lean_object* v_nextMacroScope_2788_; lean_object* v_ngen_2789_; lean_object* v_auxDeclNGen_2790_; lean_object* v_cache_2791_; lean_object* v_messages_2792_; lean_object* v_infoState_2793_; lean_object* v_snapshotTasks_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2813_; 
lean_del_object(v___x_2754_);
lean_dec(v_snd_2752_);
lean_dec(v_fst_2751_);
lean_del_object(v___x_2735_);
lean_dec_ref(v_msg_2727_);
lean_dec_ref(v_tag_2723_);
lean_dec(v_cls_2721_);
v___x_2785_ = lean_st_ref_take(v___y_2730_);
v_traceState_2786_ = lean_ctor_get(v___x_2785_, 4);
v_env_2787_ = lean_ctor_get(v___x_2785_, 0);
v_nextMacroScope_2788_ = lean_ctor_get(v___x_2785_, 1);
v_ngen_2789_ = lean_ctor_get(v___x_2785_, 2);
v_auxDeclNGen_2790_ = lean_ctor_get(v___x_2785_, 3);
v_cache_2791_ = lean_ctor_get(v___x_2785_, 5);
v_messages_2792_ = lean_ctor_get(v___x_2785_, 6);
v_infoState_2793_ = lean_ctor_get(v___x_2785_, 7);
v_snapshotTasks_2794_ = lean_ctor_get(v___x_2785_, 8);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2796_ = v___x_2785_;
v_isShared_2797_ = v_isSharedCheck_2813_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_snapshotTasks_2794_);
lean_inc(v_infoState_2793_);
lean_inc(v_messages_2792_);
lean_inc(v_cache_2791_);
lean_inc(v_traceState_2786_);
lean_inc(v_auxDeclNGen_2790_);
lean_inc(v_ngen_2789_);
lean_inc(v_nextMacroScope_2788_);
lean_inc(v_env_2787_);
lean_dec(v___x_2785_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2813_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
uint64_t v_tid_2798_; lean_object* v_traces_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2812_; 
v_tid_2798_ = lean_ctor_get_uint64(v_traceState_2786_, sizeof(void*)*1);
v_traces_2799_ = lean_ctor_get(v_traceState_2786_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_traceState_2786_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2801_ = v_traceState_2786_;
v_isShared_2802_ = v_isSharedCheck_2812_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_traces_2799_);
lean_dec(v_traceState_2786_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2812_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
v___x_2803_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2726_, v_traces_2799_);
lean_dec_ref(v_traces_2799_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2803_);
v___x_2805_ = v___x_2801_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2803_);
lean_ctor_set_uint64(v_reuseFailAlloc_2811_, sizeof(void*)*1, v_tid_2798_);
v___x_2805_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v___x_2807_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 4, v___x_2805_);
v___x_2807_ = v___x_2796_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_env_2787_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_nextMacroScope_2788_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_ngen_2789_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v_auxDeclNGen_2790_);
lean_ctor_set(v_reuseFailAlloc_2810_, 4, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2810_, 5, v_cache_2791_);
lean_ctor_set(v_reuseFailAlloc_2810_, 6, v_messages_2792_);
lean_ctor_set(v_reuseFailAlloc_2810_, 7, v_infoState_2793_);
lean_ctor_set(v_reuseFailAlloc_2810_, 8, v_snapshotTasks_2794_);
v___x_2807_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_st_ref_set(v___y_2730_, v___x_2807_);
v___x_2809_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2732_);
return v___x_2809_;
}
}
}
}
}
else
{
goto v___jp_2778_;
}
}
else
{
goto v___jp_2778_;
}
}
v___jp_2814_:
{
double v___x_2816_; double v___x_2817_; double v___x_2818_; uint8_t v___x_2819_; 
v___x_2816_ = lean_unbox_float(v_snd_2752_);
v___x_2817_ = lean_unbox_float(v_fst_2751_);
v___x_2818_ = lean_float_sub(v___x_2816_, v___x_2817_);
v___x_2819_ = lean_float_decLt(v___y_2815_, v___x_2818_);
v___y_2784_ = v___x_2819_;
goto v___jp_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_2832_, lean_object* v_collapsed_2833_, lean_object* v_tag_2834_, lean_object* v_opts_2835_, lean_object* v_clsEnabled_2836_, lean_object* v_oldTraces_2837_, lean_object* v_msg_2838_, lean_object* v_resStartStop_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
uint8_t v_collapsed_boxed_2843_; uint8_t v_clsEnabled_boxed_2844_; lean_object* v_res_2845_; 
v_collapsed_boxed_2843_ = lean_unbox(v_collapsed_2833_);
v_clsEnabled_boxed_2844_ = lean_unbox(v_clsEnabled_2836_);
v_res_2845_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_2832_, v_collapsed_boxed_2843_, v_tag_2834_, v_opts_2835_, v_clsEnabled_boxed_2844_, v_oldTraces_2837_, v_msg_2838_, v_resStartStop_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v_opts_2835_);
return v_res_2845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
lean_ctor_set(v___x_2850_, 2, v___x_2849_);
lean_ctor_set(v___x_2850_, 3, v___x_2849_);
lean_ctor_set(v___x_2850_, 4, v___x_2848_);
lean_ctor_set(v___x_2850_, 5, v___x_2848_);
lean_ctor_set(v___x_2850_, 6, v___x_2848_);
lean_ctor_set(v___x_2850_, 7, v___x_2848_);
lean_ctor_set(v___x_2850_, 8, v___x_2848_);
lean_ctor_set(v___x_2850_, 9, v___x_2848_);
return v___x_2850_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2852_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
lean_ctor_set(v___x_2852_, 2, v___x_2851_);
lean_ctor_set(v___x_2852_, 3, v___x_2851_);
lean_ctor_set(v___x_2852_, 4, v___x_2851_);
lean_ctor_set(v___x_2852_, 5, v___x_2851_);
return v___x_2852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
lean_ctor_set(v___x_2854_, 2, v___x_2853_);
lean_ctor_set(v___x_2854_, 3, v___x_2853_);
lean_ctor_set(v___x_2854_, 4, v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2855_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2856_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_2857_ = lean_box(1);
v___x_2858_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2859_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v___x_2858_);
lean_ctor_set(v___x_2860_, 2, v___x_2857_);
lean_ctor_set(v___x_2860_, 3, v___x_2856_);
lean_ctor_set(v___x_2860_, 4, v___x_2855_);
return v___x_2860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2865_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_2866_ = l_Lean_Name_append(v___x_2865_, v___x_2864_);
return v___x_2866_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2867_; double v___x_2868_; 
v___x_2867_ = lean_unsigned_to_nat(1000000000u);
v___x_2868_ = lean_float_of_nat(v___x_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_2869_, lean_object* v_name_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_options_2874_; uint8_t v_hasTrace_2875_; 
v_options_2874_ = lean_ctor_get(v___y_2871_, 2);
v_hasTrace_2875_ = lean_ctor_get_uint8(v_options_2874_, sizeof(void*)*1);
if (v_hasTrace_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v_env_2877_; lean_object* v___x_2878_; 
lean_dec_ref(v___f_2869_);
v___x_2876_ = lean_st_ref_get(v___y_2872_);
v_env_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc_ref(v_env_2877_);
lean_dec(v___x_2876_);
lean_inc(v_name_2870_);
v___x_2878_ = l_Lean_Meta_declFromEqLikeName(v_env_2877_, v_name_2870_);
if (lean_obj_tag(v___x_2878_) == 1)
{
lean_object* v_val_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2978_; 
v_val_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2978_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_val_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2978_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_fst_2883_; lean_object* v_snd_2884_; lean_object* v___x_2885_; lean_object* v_env_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_fst_2883_ = lean_ctor_get(v_val_2879_, 0);
lean_inc_n(v_fst_2883_, 2);
v_snd_2884_ = lean_ctor_get(v_val_2879_, 1);
lean_inc_n(v_snd_2884_, 2);
lean_dec(v_val_2879_);
v___x_2885_ = lean_st_ref_get(v___y_2872_);
v_env_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc_ref(v_env_2886_);
lean_dec(v___x_2885_);
v___x_2887_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2886_, v_fst_2883_, v_snd_2884_);
v___x_2888_ = lean_name_eq(v_name_2870_, v___x_2887_);
lean_dec(v___x_2887_);
lean_dec(v_name_2870_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
lean_dec(v_snd_2884_);
lean_dec(v_fst_2883_);
v___x_2889_ = lean_box(v_hasTrace_2875_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2889_);
v___x_2891_ = v___x_2881_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
else
{
uint8_t v___x_2893_; lean_object* v_a_2895_; 
lean_inc(v_snd_2884_);
v___x_2893_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_2884_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2909_; uint8_t v___x_2910_; lean_object* v_a_2912_; 
lean_del_object(v___x_2881_);
v___x_2909_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_2910_ = lean_string_dec_eq(v_snd_2884_, v___x_2909_);
lean_dec(v_snd_2884_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_dec(v_fst_2883_);
v___x_2924_ = lean_box(v_hasTrace_2875_);
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
return v___x_2925_;
}
else
{
uint8_t v___x_2926_; uint8_t v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; uint64_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2926_ = 1;
v___x_2927_ = 0;
v___x_2928_ = 2;
v___x_2929_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2929_, 0, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2929_, 1, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2929_, 2, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2929_, 3, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2929_, 4, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2929_, 5, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 6, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 7, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2929_, 8, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 9, v___x_2926_);
lean_ctor_set_uint8(v___x_2929_, 10, v___x_2927_);
lean_ctor_set_uint8(v___x_2929_, 11, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 12, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 13, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 14, v___x_2928_);
lean_ctor_set_uint8(v___x_2929_, 15, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 16, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 17, v___x_2910_);
lean_ctor_set_uint8(v___x_2929_, 18, v___x_2910_);
v___x_2930_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2929_);
v___x_2931_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set_uint64(v___x_2931_, sizeof(void*)*1, v___x_2930_);
v___x_2932_ = lean_box(1);
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2935_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2936_ = lean_box(0);
v___x_2937_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2937_, 0, v___x_2931_);
lean_ctor_set(v___x_2937_, 1, v___x_2932_);
lean_ctor_set(v___x_2937_, 2, v___x_2934_);
lean_ctor_set(v___x_2937_, 3, v___x_2935_);
lean_ctor_set(v___x_2937_, 4, v___x_2936_);
lean_ctor_set(v___x_2937_, 5, v___x_2933_);
lean_ctor_set(v___x_2937_, 6, v___x_2936_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*7, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*7 + 1, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*7 + 2, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*7 + 3, v___x_2888_);
v___x_2938_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2939_ = lean_st_mk_ref(v___x_2938_);
v___x_2940_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_2883_, v___x_2888_, v___x_2937_, v___x_2939_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___x_2937_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = lean_st_ref_get(v___x_2939_);
lean_dec(v___x_2939_);
lean_dec(v___x_2942_);
v_a_2912_ = v_a_2941_;
goto v___jp_2911_;
}
else
{
lean_dec(v___x_2939_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2943_; 
v_a_2943_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2940_);
v_a_2912_ = v_a_2943_;
goto v___jp_2911_;
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
v_a_2944_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2940_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2940_);
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
}
v___jp_2911_:
{
if (lean_obj_tag(v_a_2912_) == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_box(v_hasTrace_2875_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
else
{
lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2922_; 
v_isSharedCheck_2922_ = !lean_is_exclusive(v_a_2912_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v_a_2912_, 0);
lean_dec(v_unused_2923_);
v___x_2916_ = v_a_2912_;
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
else
{
lean_dec(v_a_2912_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2918_ = lean_box(v___x_2910_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set_tag(v___x_2916_, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2918_);
v___x_2920_ = v___x_2916_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
else
{
uint8_t v___x_2952_; uint8_t v___x_2953_; uint8_t v___x_2954_; lean_object* v___x_2955_; uint64_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
lean_dec(v_snd_2884_);
v___x_2952_ = 1;
v___x_2953_ = 0;
v___x_2954_ = 2;
v___x_2955_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2955_, 0, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2955_, 1, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2955_, 2, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2955_, 3, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2955_, 4, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2955_, 5, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 6, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 7, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2955_, 8, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 9, v___x_2952_);
lean_ctor_set_uint8(v___x_2955_, 10, v___x_2953_);
lean_ctor_set_uint8(v___x_2955_, 11, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 12, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 13, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 14, v___x_2954_);
lean_ctor_set_uint8(v___x_2955_, 15, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 16, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 17, v___x_2893_);
lean_ctor_set_uint8(v___x_2955_, 18, v___x_2893_);
v___x_2956_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2955_);
v___x_2957_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set_uint64(v___x_2957_, sizeof(void*)*1, v___x_2956_);
v___x_2958_ = lean_box(1);
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2961_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2963_, 0, v___x_2957_);
lean_ctor_set(v___x_2963_, 1, v___x_2958_);
lean_ctor_set(v___x_2963_, 2, v___x_2960_);
lean_ctor_set(v___x_2963_, 3, v___x_2961_);
lean_ctor_set(v___x_2963_, 4, v___x_2962_);
lean_ctor_set(v___x_2963_, 5, v___x_2959_);
lean_ctor_set(v___x_2963_, 6, v___x_2962_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*7, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*7 + 1, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*7 + 2, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*7 + 3, v___x_2888_);
v___x_2964_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2965_ = lean_st_mk_ref(v___x_2964_);
v___x_2966_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_2883_, v___x_2963_, v___x_2965_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___x_2963_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref(v___x_2966_);
v___x_2968_ = lean_st_ref_get(v___x_2965_);
lean_dec(v___x_2965_);
lean_dec(v___x_2968_);
v_a_2895_ = v_a_2967_;
goto v___jp_2894_;
}
else
{
lean_dec(v___x_2965_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2969_; 
v_a_2969_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2969_);
lean_dec_ref(v___x_2966_);
v_a_2895_ = v_a_2969_;
goto v___jp_2894_;
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_del_object(v___x_2881_);
v_a_2970_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2966_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2966_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
v___jp_2894_:
{
if (lean_obj_tag(v_a_2895_) == 0)
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = lean_box(v_hasTrace_2875_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2896_);
v___x_2898_ = v___x_2881_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
else
{
lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2907_; 
lean_del_object(v___x_2881_);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_a_2895_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v_a_2895_, 0);
lean_dec(v_unused_2908_);
v___x_2901_ = v_a_2895_;
v_isShared_2902_ = v_isSharedCheck_2907_;
goto v_resetjp_2900_;
}
else
{
lean_dec(v_a_2895_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2907_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2903_ = lean_box(v___x_2893_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set_tag(v___x_2901_, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2903_);
v___x_2905_ = v___x_2901_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_dec(v___x_2878_);
lean_dec(v_name_2870_);
v___x_2979_ = lean_box(v_hasTrace_2875_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v_a_2990_; lean_object* v___y_3003_; lean_object* v___y_3004_; uint8_t v_a_3005_; lean_object* v___y_3009_; uint8_t v___y_3010_; lean_object* v___y_3011_; lean_object* v_a_3012_; lean_object* v___y_3014_; uint8_t v___y_3015_; lean_object* v___y_3016_; lean_object* v_a_3017_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v_a_3021_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v_a_3026_; lean_object* v___y_3036_; lean_object* v___y_3037_; uint8_t v_a_3038_; uint8_t v___y_3042_; uint8_t v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v_a_3046_; uint8_t v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v_a_3051_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v_a_3056_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; 
v_inheritedTraceOptions_2981_ = lean_ctor_get(v___y_2871_, 13);
lean_inc(v_name_2870_);
v___f_2982_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_2982_, 0, v_name_2870_);
v___x_2983_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2984_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1));
v___x_2985_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2986_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2981_, v_options_2874_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_3181_; uint8_t v___x_3182_; lean_object* v_a_3184_; lean_object* v_a_3197_; 
v___x_3181_ = l_Lean_trace_profiler;
v___x_3182_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_2874_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3209_; lean_object* v_env_3210_; lean_object* v___x_3211_; 
lean_dec_ref(v___f_2982_);
lean_dec_ref(v___f_2869_);
v___x_3209_ = lean_st_ref_get(v___y_2872_);
v_env_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc_ref(v_env_3210_);
lean_dec(v___x_3209_);
lean_inc(v_name_2870_);
v___x_3211_ = l_Lean_Meta_declFromEqLikeName(v_env_3210_, v_name_2870_);
if (lean_obj_tag(v___x_3211_) == 1)
{
lean_object* v_val_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3285_; 
v_val_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3285_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_val_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3285_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v_fst_3216_; lean_object* v_snd_3217_; lean_object* v___x_3218_; lean_object* v_env_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v_fst_3216_ = lean_ctor_get(v_val_3212_, 0);
lean_inc_n(v_fst_3216_, 2);
v_snd_3217_ = lean_ctor_get(v_val_3212_, 1);
lean_inc_n(v_snd_3217_, 2);
lean_dec(v_val_3212_);
v___x_3218_ = lean_st_ref_get(v___y_2872_);
v_env_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc_ref(v_env_3219_);
lean_dec(v___x_3218_);
v___x_3220_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3219_, v_fst_3216_, v_snd_3217_);
v___x_3221_ = lean_name_eq(v_name_2870_, v___x_3220_);
lean_dec(v___x_3220_);
lean_dec(v_name_2870_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
lean_dec(v_snd_3217_);
lean_dec(v_fst_3216_);
v___x_3222_ = lean_box(v___x_3182_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3222_);
v___x_3224_ = v___x_3214_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
else
{
uint8_t v___x_3226_; 
lean_inc(v_snd_3217_);
v___x_3226_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3217_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3227_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3228_ = lean_string_dec_eq(v_snd_3217_, v___x_3227_);
lean_dec(v_snd_3217_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
lean_dec(v_fst_3216_);
v___x_3229_ = lean_box(v___x_3182_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3229_);
v___x_3231_ = v___x_3214_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
else
{
uint8_t v___x_3233_; uint8_t v___x_3234_; uint8_t v___x_3235_; lean_object* v___x_3236_; uint64_t v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_del_object(v___x_3214_);
v___x_3233_ = 1;
v___x_3234_ = 0;
v___x_3235_ = 2;
v___x_3236_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3236_, 0, v___x_3182_);
lean_ctor_set_uint8(v___x_3236_, 1, v___x_3182_);
lean_ctor_set_uint8(v___x_3236_, 2, v___x_3182_);
lean_ctor_set_uint8(v___x_3236_, 3, v___x_3182_);
lean_ctor_set_uint8(v___x_3236_, 4, v___x_3182_);
lean_ctor_set_uint8(v___x_3236_, 5, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 6, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 7, v___x_3182_);
lean_ctor_set_uint8(v___x_3236_, 8, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 9, v___x_3233_);
lean_ctor_set_uint8(v___x_3236_, 10, v___x_3234_);
lean_ctor_set_uint8(v___x_3236_, 11, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 12, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 13, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 14, v___x_3235_);
lean_ctor_set_uint8(v___x_3236_, 15, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 16, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 17, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3236_, 18, v_hasTrace_2875_);
v___x_3237_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3236_);
v___x_3238_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set_uint64(v___x_3238_, sizeof(void*)*1, v___x_3237_);
v___x_3239_ = lean_box(1);
v___x_3240_ = lean_unsigned_to_nat(0u);
v___x_3241_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3242_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3243_ = lean_box(0);
v___x_3244_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3244_, 0, v___x_3238_);
lean_ctor_set(v___x_3244_, 1, v___x_3239_);
lean_ctor_set(v___x_3244_, 2, v___x_3241_);
lean_ctor_set(v___x_3244_, 3, v___x_3242_);
lean_ctor_set(v___x_3244_, 4, v___x_3243_);
lean_ctor_set(v___x_3244_, 5, v___x_3240_);
lean_ctor_set(v___x_3244_, 6, v___x_3243_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*7, v___x_3182_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*7 + 1, v___x_3182_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*7 + 2, v___x_3182_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*7 + 3, v_hasTrace_2875_);
v___x_3245_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3246_ = lean_st_mk_ref(v___x_3245_);
v___x_3247_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3216_, v_hasTrace_2875_, v___x_3244_, v___x_3246_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___x_3244_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3249_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref(v___x_3247_);
v___x_3249_ = lean_st_ref_get(v___x_3246_);
lean_dec(v___x_3246_);
lean_dec(v___x_3249_);
v_a_3197_ = v_a_3248_;
goto v___jp_3196_;
}
else
{
lean_dec(v___x_3246_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3250_; 
v_a_3250_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___x_3247_);
v_a_3197_ = v_a_3250_;
goto v___jp_3196_;
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
v_a_3251_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3247_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3247_);
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
}
}
else
{
uint8_t v___x_3259_; uint8_t v___x_3260_; uint8_t v___x_3261_; lean_object* v___x_3262_; uint64_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v_snd_3217_);
lean_del_object(v___x_3214_);
v___x_3259_ = 1;
v___x_3260_ = 0;
v___x_3261_ = 2;
v___x_3262_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3262_, 0, v___x_3182_);
lean_ctor_set_uint8(v___x_3262_, 1, v___x_3182_);
lean_ctor_set_uint8(v___x_3262_, 2, v___x_3182_);
lean_ctor_set_uint8(v___x_3262_, 3, v___x_3182_);
lean_ctor_set_uint8(v___x_3262_, 4, v___x_3182_);
lean_ctor_set_uint8(v___x_3262_, 5, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 6, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 7, v___x_3182_);
lean_ctor_set_uint8(v___x_3262_, 8, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 9, v___x_3259_);
lean_ctor_set_uint8(v___x_3262_, 10, v___x_3260_);
lean_ctor_set_uint8(v___x_3262_, 11, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 12, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 13, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 14, v___x_3261_);
lean_ctor_set_uint8(v___x_3262_, 15, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 16, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 17, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3262_, 18, v_hasTrace_2875_);
v___x_3263_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3262_);
v___x_3264_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set_uint64(v___x_3264_, sizeof(void*)*1, v___x_3263_);
v___x_3265_ = lean_box(1);
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3268_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3269_ = lean_box(0);
v___x_3270_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3270_, 0, v___x_3264_);
lean_ctor_set(v___x_3270_, 1, v___x_3265_);
lean_ctor_set(v___x_3270_, 2, v___x_3267_);
lean_ctor_set(v___x_3270_, 3, v___x_3268_);
lean_ctor_set(v___x_3270_, 4, v___x_3269_);
lean_ctor_set(v___x_3270_, 5, v___x_3266_);
lean_ctor_set(v___x_3270_, 6, v___x_3269_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*7, v___x_3182_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*7 + 1, v___x_3182_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*7 + 2, v___x_3182_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*7 + 3, v_hasTrace_2875_);
v___x_3271_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3272_ = lean_st_mk_ref(v___x_3271_);
v___x_3273_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3216_, v___x_3270_, v___x_3272_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___x_3270_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3275_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref(v___x_3273_);
v___x_3275_ = lean_st_ref_get(v___x_3272_);
lean_dec(v___x_3272_);
lean_dec(v___x_3275_);
v_a_3184_ = v_a_3274_;
goto v___jp_3183_;
}
else
{
lean_dec(v___x_3272_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3276_; 
v_a_3276_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3276_);
lean_dec_ref(v___x_3273_);
v_a_3184_ = v_a_3276_;
goto v___jp_3183_;
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
v_a_3277_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3273_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3273_);
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
}
}
}
else
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_dec(v___x_3211_);
lean_dec(v_name_2870_);
v___x_3286_ = lean_box(v___x_3182_);
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
}
else
{
goto v___jp_3065_;
}
v___jp_3183_:
{
if (lean_obj_tag(v_a_3184_) == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_box(v___x_3182_);
v___x_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
return v___x_3186_;
}
else
{
lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3194_; 
v_isSharedCheck_3194_ = !lean_is_exclusive(v_a_3184_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v_a_3184_, 0);
lean_dec(v_unused_3195_);
v___x_3188_ = v_a_3184_;
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
else
{
lean_dec(v_a_3184_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_box(v_hasTrace_2875_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set_tag(v___x_3188_, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3190_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
v___jp_3196_:
{
if (lean_obj_tag(v_a_3197_) == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_box(v___x_3182_);
v___x_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
return v___x_3199_;
}
else
{
lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
v_isSharedCheck_3207_ = !lean_is_exclusive(v_a_3197_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v_a_3197_, 0);
lean_dec(v_unused_3208_);
v___x_3201_ = v_a_3197_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_dec(v_a_3197_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_box(v_hasTrace_2875_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set_tag(v___x_3201_, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
goto v___jp_3065_;
}
v___jp_2987_:
{
lean_object* v___x_2991_; double v___x_2992_; double v___x_2993_; double v___x_2994_; double v___x_2995_; double v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2991_ = lean_io_mono_nanos_now();
v___x_2992_ = lean_float_of_nat(v___y_2988_);
v___x_2993_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2994_ = lean_float_div(v___x_2992_, v___x_2993_);
v___x_2995_ = lean_float_of_nat(v___x_2991_);
v___x_2996_ = lean_float_div(v___x_2995_, v___x_2993_);
v___x_2997_ = lean_box_float(v___x_2994_);
v___x_2998_ = lean_box_float(v___x_2996_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v_a_2990_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_2983_, v_hasTrace_2875_, v___x_2984_, v_options_2874_, v___x_2986_, v___y_2989_, v___f_2982_, v___x_3000_, v___y_2871_, v___y_2872_);
return v___x_3001_;
}
v___jp_3002_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_box(v_a_3005_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
v___y_2988_ = v___y_3003_;
v___y_2989_ = v___y_3004_;
v_a_2990_ = v___x_3007_;
goto v___jp_2987_;
}
v___jp_3008_:
{
if (lean_obj_tag(v_a_3012_) == 0)
{
v___y_3003_ = v___y_3009_;
v___y_3004_ = v___y_3011_;
v_a_3005_ = v___y_3010_;
goto v___jp_3002_;
}
else
{
lean_dec_ref(v_a_3012_);
v___y_3003_ = v___y_3009_;
v___y_3004_ = v___y_3011_;
v_a_3005_ = v_hasTrace_2875_;
goto v___jp_3002_;
}
}
v___jp_3013_:
{
if (lean_obj_tag(v_a_3017_) == 0)
{
v___y_3003_ = v___y_3014_;
v___y_3004_ = v___y_3016_;
v_a_3005_ = v___y_3015_;
goto v___jp_3002_;
}
else
{
lean_dec_ref(v_a_3017_);
v___y_3003_ = v___y_3014_;
v___y_3004_ = v___y_3016_;
v_a_3005_ = v_hasTrace_2875_;
goto v___jp_3002_;
}
}
v___jp_3018_:
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_a_3021_);
v___y_2988_ = v___y_3019_;
v___y_2989_ = v___y_3020_;
v_a_2990_ = v___x_3022_;
goto v___jp_2987_;
}
v___jp_3023_:
{
lean_object* v___x_3027_; double v___x_3028_; double v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3027_ = lean_io_get_num_heartbeats();
v___x_3028_ = lean_float_of_nat(v___y_3024_);
v___x_3029_ = lean_float_of_nat(v___x_3027_);
v___x_3030_ = lean_box_float(v___x_3028_);
v___x_3031_ = lean_box_float(v___x_3029_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_a_3026_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_2983_, v_hasTrace_2875_, v___x_2984_, v_options_2874_, v___x_2986_, v___y_3025_, v___f_2982_, v___x_3033_, v___y_2871_, v___y_2872_);
return v___x_3034_;
}
v___jp_3035_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_box(v_a_3038_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
v___y_3024_ = v___y_3036_;
v___y_3025_ = v___y_3037_;
v_a_3026_ = v___x_3040_;
goto v___jp_3023_;
}
v___jp_3041_:
{
if (lean_obj_tag(v_a_3046_) == 0)
{
v___y_3036_ = v___y_3044_;
v___y_3037_ = v___y_3045_;
v_a_3038_ = v___y_3042_;
goto v___jp_3035_;
}
else
{
lean_dec_ref(v_a_3046_);
v___y_3036_ = v___y_3044_;
v___y_3037_ = v___y_3045_;
v_a_3038_ = v___y_3043_;
goto v___jp_3035_;
}
}
v___jp_3047_:
{
if (lean_obj_tag(v_a_3051_) == 0)
{
uint8_t v___x_3052_; 
v___x_3052_ = 0;
v___y_3036_ = v___y_3049_;
v___y_3037_ = v___y_3050_;
v_a_3038_ = v___x_3052_;
goto v___jp_3035_;
}
else
{
lean_dec_ref(v_a_3051_);
v___y_3036_ = v___y_3049_;
v___y_3037_ = v___y_3050_;
v_a_3038_ = v___y_3048_;
goto v___jp_3035_;
}
}
v___jp_3053_:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_a_3056_);
v___y_3024_ = v___y_3054_;
v___y_3025_ = v___y_3055_;
v_a_3026_ = v___x_3057_;
goto v___jp_3023_;
}
v___jp_3058_:
{
if (lean_obj_tag(v___y_3061_) == 0)
{
lean_object* v_a_3062_; uint8_t v___x_3063_; 
v_a_3062_ = lean_ctor_get(v___y_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref(v___y_3061_);
v___x_3063_ = lean_unbox(v_a_3062_);
lean_dec(v_a_3062_);
v___y_3036_ = v___y_3059_;
v___y_3037_ = v___y_3060_;
v_a_3038_ = v___x_3063_;
goto v___jp_3035_;
}
else
{
lean_object* v_a_3064_; 
v_a_3064_ = lean_ctor_get(v___y_3061_, 0);
lean_inc(v_a_3064_);
lean_dec_ref(v___y_3061_);
v___y_3054_ = v___y_3059_;
v___y_3055_ = v___y_3060_;
v_a_3056_ = v_a_3064_;
goto v___jp_3053_;
}
}
v___jp_3065_:
{
lean_object* v___x_3066_; lean_object* v_a_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3066_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2872_);
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref(v___x_3066_);
v___x_3068_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3069_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_2874_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v_env_3072_; lean_object* v___x_3073_; 
lean_dec_ref(v___f_2869_);
v___x_3070_ = lean_io_mono_nanos_now();
v___x_3071_ = lean_st_ref_get(v___y_2872_);
v_env_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc_ref(v_env_3072_);
lean_dec(v___x_3071_);
lean_inc(v_name_2870_);
v___x_3073_ = l_Lean_Meta_declFromEqLikeName(v_env_3072_, v_name_2870_);
if (lean_obj_tag(v___x_3073_) == 1)
{
lean_object* v_val_3074_; lean_object* v_fst_3075_; lean_object* v_snd_3076_; lean_object* v___x_3077_; lean_object* v_env_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v_val_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_val_3074_);
lean_dec_ref(v___x_3073_);
v_fst_3075_ = lean_ctor_get(v_val_3074_, 0);
lean_inc_n(v_fst_3075_, 2);
v_snd_3076_ = lean_ctor_get(v_val_3074_, 1);
lean_inc_n(v_snd_3076_, 2);
lean_dec(v_val_3074_);
v___x_3077_ = lean_st_ref_get(v___y_2872_);
v_env_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_env_3078_);
lean_dec(v___x_3077_);
v___x_3079_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3078_, v_fst_3075_, v_snd_3076_);
v___x_3080_ = lean_name_eq(v_name_2870_, v___x_3079_);
lean_dec(v___x_3079_);
lean_dec(v_name_2870_);
if (v___x_3080_ == 0)
{
lean_dec(v_snd_3076_);
lean_dec(v_fst_3075_);
v___y_3003_ = v___x_3070_;
v___y_3004_ = v_a_3067_;
v_a_3005_ = v___x_3069_;
goto v___jp_3002_;
}
else
{
uint8_t v___x_3081_; 
lean_inc(v_snd_3076_);
v___x_3081_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3076_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3083_ = lean_string_dec_eq(v_snd_3076_, v___x_3082_);
lean_dec(v_snd_3076_);
if (v___x_3083_ == 0)
{
lean_dec(v_fst_3075_);
v___y_3003_ = v___x_3070_;
v___y_3004_ = v_a_3067_;
v_a_3005_ = v___x_3069_;
goto v___jp_3002_;
}
else
{
uint8_t v___x_3084_; uint8_t v___x_3085_; uint8_t v___x_3086_; lean_object* v___x_3087_; uint64_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3084_ = 1;
v___x_3085_ = 0;
v___x_3086_ = 2;
v___x_3087_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3087_, 0, v___x_3069_);
lean_ctor_set_uint8(v___x_3087_, 1, v___x_3069_);
lean_ctor_set_uint8(v___x_3087_, 2, v___x_3069_);
lean_ctor_set_uint8(v___x_3087_, 3, v___x_3069_);
lean_ctor_set_uint8(v___x_3087_, 4, v___x_3069_);
lean_ctor_set_uint8(v___x_3087_, 5, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 6, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 7, v___x_3069_);
lean_ctor_set_uint8(v___x_3087_, 8, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 9, v___x_3084_);
lean_ctor_set_uint8(v___x_3087_, 10, v___x_3085_);
lean_ctor_set_uint8(v___x_3087_, 11, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 12, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 13, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 14, v___x_3086_);
lean_ctor_set_uint8(v___x_3087_, 15, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 16, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 17, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3087_, 18, v_hasTrace_2875_);
v___x_3088_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3087_);
v___x_3089_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3089_, 0, v___x_3087_);
lean_ctor_set_uint64(v___x_3089_, sizeof(void*)*1, v___x_3088_);
v___x_3090_ = lean_box(1);
v___x_3091_ = lean_unsigned_to_nat(0u);
v___x_3092_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3093_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3094_ = lean_box(0);
v___x_3095_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3095_, 0, v___x_3089_);
lean_ctor_set(v___x_3095_, 1, v___x_3090_);
lean_ctor_set(v___x_3095_, 2, v___x_3092_);
lean_ctor_set(v___x_3095_, 3, v___x_3093_);
lean_ctor_set(v___x_3095_, 4, v___x_3094_);
lean_ctor_set(v___x_3095_, 5, v___x_3091_);
lean_ctor_set(v___x_3095_, 6, v___x_3094_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*7, v___x_3069_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*7 + 1, v___x_3069_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*7 + 2, v___x_3069_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*7 + 3, v_hasTrace_2875_);
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3097_ = lean_st_mk_ref(v___x_3096_);
v___x_3098_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3075_, v_hasTrace_2875_, v___x_3095_, v___x_3097_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___x_3095_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v___x_3100_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
lean_dec_ref(v___x_3098_);
v___x_3100_ = lean_st_ref_get(v___x_3097_);
lean_dec(v___x_3097_);
lean_dec(v___x_3100_);
v___y_3014_ = v___x_3070_;
v___y_3015_ = v___x_3069_;
v___y_3016_ = v_a_3067_;
v_a_3017_ = v_a_3099_;
goto v___jp_3013_;
}
else
{
lean_dec(v___x_3097_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3101_; 
v_a_3101_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3101_);
lean_dec_ref(v___x_3098_);
v___y_3014_ = v___x_3070_;
v___y_3015_ = v___x_3069_;
v___y_3016_ = v_a_3067_;
v_a_3017_ = v_a_3101_;
goto v___jp_3013_;
}
else
{
lean_object* v_a_3102_; 
v_a_3102_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3102_);
lean_dec_ref(v___x_3098_);
v___y_3019_ = v___x_3070_;
v___y_3020_ = v_a_3067_;
v_a_3021_ = v_a_3102_;
goto v___jp_3018_;
}
}
}
}
else
{
uint8_t v___x_3103_; uint8_t v___x_3104_; uint8_t v___x_3105_; lean_object* v___x_3106_; uint64_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec(v_snd_3076_);
v___x_3103_ = 1;
v___x_3104_ = 0;
v___x_3105_ = 2;
v___x_3106_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3106_, 0, v___x_3069_);
lean_ctor_set_uint8(v___x_3106_, 1, v___x_3069_);
lean_ctor_set_uint8(v___x_3106_, 2, v___x_3069_);
lean_ctor_set_uint8(v___x_3106_, 3, v___x_3069_);
lean_ctor_set_uint8(v___x_3106_, 4, v___x_3069_);
lean_ctor_set_uint8(v___x_3106_, 5, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 6, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 7, v___x_3069_);
lean_ctor_set_uint8(v___x_3106_, 8, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 9, v___x_3103_);
lean_ctor_set_uint8(v___x_3106_, 10, v___x_3104_);
lean_ctor_set_uint8(v___x_3106_, 11, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 12, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 13, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 14, v___x_3105_);
lean_ctor_set_uint8(v___x_3106_, 15, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 16, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 17, v_hasTrace_2875_);
lean_ctor_set_uint8(v___x_3106_, 18, v_hasTrace_2875_);
v___x_3107_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set_uint64(v___x_3108_, sizeof(void*)*1, v___x_3107_);
v___x_3109_ = lean_box(1);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3112_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3113_ = lean_box(0);
v___x_3114_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3114_, 0, v___x_3108_);
lean_ctor_set(v___x_3114_, 1, v___x_3109_);
lean_ctor_set(v___x_3114_, 2, v___x_3111_);
lean_ctor_set(v___x_3114_, 3, v___x_3112_);
lean_ctor_set(v___x_3114_, 4, v___x_3113_);
lean_ctor_set(v___x_3114_, 5, v___x_3110_);
lean_ctor_set(v___x_3114_, 6, v___x_3113_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*7, v___x_3069_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*7 + 1, v___x_3069_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*7 + 2, v___x_3069_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*7 + 3, v_hasTrace_2875_);
v___x_3115_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3116_ = lean_st_mk_ref(v___x_3115_);
v___x_3117_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3075_, v___x_3114_, v___x_3116_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___x_3114_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref(v___x_3117_);
v___x_3119_ = lean_st_ref_get(v___x_3116_);
lean_dec(v___x_3116_);
lean_dec(v___x_3119_);
v___y_3009_ = v___x_3070_;
v___y_3010_ = v___x_3069_;
v___y_3011_ = v_a_3067_;
v_a_3012_ = v_a_3118_;
goto v___jp_3008_;
}
else
{
lean_dec(v___x_3116_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3120_; 
v_a_3120_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3120_);
lean_dec_ref(v___x_3117_);
v___y_3009_ = v___x_3070_;
v___y_3010_ = v___x_3069_;
v___y_3011_ = v_a_3067_;
v_a_3012_ = v_a_3120_;
goto v___jp_3008_;
}
else
{
lean_object* v_a_3121_; 
v_a_3121_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3121_);
lean_dec_ref(v___x_3117_);
v___y_3019_ = v___x_3070_;
v___y_3020_ = v_a_3067_;
v_a_3021_ = v_a_3121_;
goto v___jp_3018_;
}
}
}
}
}
else
{
lean_dec(v___x_3073_);
lean_dec(v_name_2870_);
v___y_3003_ = v___x_3070_;
v___y_3004_ = v_a_3067_;
v_a_3005_ = v___x_3069_;
goto v___jp_3002_;
}
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v_env_3124_; lean_object* v___x_3125_; 
v___x_3122_ = lean_io_get_num_heartbeats();
v___x_3123_ = lean_st_ref_get(v___y_2872_);
v_env_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc_ref(v_env_3124_);
lean_dec(v___x_3123_);
lean_inc(v_name_2870_);
v___x_3125_ = l_Lean_Meta_declFromEqLikeName(v_env_3124_, v_name_2870_);
if (lean_obj_tag(v___x_3125_) == 1)
{
lean_object* v_val_3126_; lean_object* v_fst_3127_; lean_object* v_snd_3128_; lean_object* v___x_3129_; lean_object* v_env_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v_val_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_val_3126_);
lean_dec_ref(v___x_3125_);
v_fst_3127_ = lean_ctor_get(v_val_3126_, 0);
lean_inc_n(v_fst_3127_, 2);
v_snd_3128_ = lean_ctor_get(v_val_3126_, 1);
lean_inc_n(v_snd_3128_, 2);
lean_dec(v_val_3126_);
v___x_3129_ = lean_st_ref_get(v___y_2872_);
v_env_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc_ref(v_env_3130_);
lean_dec(v___x_3129_);
v___x_3131_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3130_, v_fst_3127_, v_snd_3128_);
v___x_3132_ = lean_name_eq(v_name_2870_, v___x_3131_);
lean_dec(v___x_3131_);
lean_dec(v_name_2870_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
v___x_3133_ = lean_box(0);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_3134_ = lean_apply_4(v___f_2869_, v___x_3133_, v___y_2871_, v___y_2872_, lean_box(0));
v___y_3059_ = v___x_3122_;
v___y_3060_ = v_a_3067_;
v___y_3061_ = v___x_3134_;
goto v___jp_3058_;
}
else
{
uint8_t v___x_3135_; 
lean_inc(v_snd_3128_);
v___x_3135_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3128_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3137_ = lean_string_dec_eq(v_snd_3128_, v___x_3136_);
lean_dec(v_snd_3128_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_dec(v_fst_3127_);
v___x_3138_ = lean_box(0);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_3139_ = lean_apply_4(v___f_2869_, v___x_3138_, v___y_2871_, v___y_2872_, lean_box(0));
v___y_3059_ = v___x_3122_;
v___y_3060_ = v_a_3067_;
v___y_3061_ = v___x_3139_;
goto v___jp_3058_;
}
else
{
uint8_t v___x_3140_; uint8_t v___x_3141_; uint8_t v___x_3142_; lean_object* v___x_3143_; uint64_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v___f_2869_);
v___x_3140_ = 1;
v___x_3141_ = 0;
v___x_3142_ = 2;
v___x_3143_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3143_, 0, v___x_3135_);
lean_ctor_set_uint8(v___x_3143_, 1, v___x_3135_);
lean_ctor_set_uint8(v___x_3143_, 2, v___x_3135_);
lean_ctor_set_uint8(v___x_3143_, 3, v___x_3135_);
lean_ctor_set_uint8(v___x_3143_, 4, v___x_3135_);
lean_ctor_set_uint8(v___x_3143_, 5, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 6, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 7, v___x_3135_);
lean_ctor_set_uint8(v___x_3143_, 8, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 9, v___x_3140_);
lean_ctor_set_uint8(v___x_3143_, 10, v___x_3141_);
lean_ctor_set_uint8(v___x_3143_, 11, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 12, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 13, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 14, v___x_3142_);
lean_ctor_set_uint8(v___x_3143_, 15, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 16, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 17, v___x_3069_);
lean_ctor_set_uint8(v___x_3143_, 18, v___x_3069_);
v___x_3144_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3145_, 0, v___x_3143_);
lean_ctor_set_uint64(v___x_3145_, sizeof(void*)*1, v___x_3144_);
v___x_3146_ = lean_box(1);
v___x_3147_ = lean_unsigned_to_nat(0u);
v___x_3148_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3149_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3150_ = lean_box(0);
v___x_3151_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3151_, 0, v___x_3145_);
lean_ctor_set(v___x_3151_, 1, v___x_3146_);
lean_ctor_set(v___x_3151_, 2, v___x_3148_);
lean_ctor_set(v___x_3151_, 3, v___x_3149_);
lean_ctor_set(v___x_3151_, 4, v___x_3150_);
lean_ctor_set(v___x_3151_, 5, v___x_3147_);
lean_ctor_set(v___x_3151_, 6, v___x_3150_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*7, v___x_3135_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*7 + 1, v___x_3135_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*7 + 2, v___x_3135_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*7 + 3, v___x_3069_);
v___x_3152_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3153_ = lean_st_mk_ref(v___x_3152_);
v___x_3154_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3127_, v___x_3069_, v___x_3151_, v___x_3153_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___x_3151_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref(v___x_3154_);
v___x_3156_ = lean_st_ref_get(v___x_3153_);
lean_dec(v___x_3153_);
lean_dec(v___x_3156_);
v___y_3042_ = v___x_3135_;
v___y_3043_ = v___x_3069_;
v___y_3044_ = v___x_3122_;
v___y_3045_ = v_a_3067_;
v_a_3046_ = v_a_3155_;
goto v___jp_3041_;
}
else
{
lean_dec(v___x_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3157_; 
v_a_3157_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3157_);
lean_dec_ref(v___x_3154_);
v___y_3042_ = v___x_3135_;
v___y_3043_ = v___x_3069_;
v___y_3044_ = v___x_3122_;
v___y_3045_ = v_a_3067_;
v_a_3046_ = v_a_3157_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3158_; 
v_a_3158_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3158_);
lean_dec_ref(v___x_3154_);
v___y_3054_ = v___x_3122_;
v___y_3055_ = v_a_3067_;
v_a_3056_ = v_a_3158_;
goto v___jp_3053_;
}
}
}
}
else
{
uint8_t v___x_3159_; uint8_t v___x_3160_; uint8_t v___x_3161_; uint8_t v___x_3162_; lean_object* v___x_3163_; uint64_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec(v_snd_3128_);
lean_dec_ref(v___f_2869_);
v___x_3159_ = 0;
v___x_3160_ = 1;
v___x_3161_ = 0;
v___x_3162_ = 2;
v___x_3163_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3163_, 0, v___x_3159_);
lean_ctor_set_uint8(v___x_3163_, 1, v___x_3159_);
lean_ctor_set_uint8(v___x_3163_, 2, v___x_3159_);
lean_ctor_set_uint8(v___x_3163_, 3, v___x_3159_);
lean_ctor_set_uint8(v___x_3163_, 4, v___x_3159_);
lean_ctor_set_uint8(v___x_3163_, 5, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 6, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 7, v___x_3159_);
lean_ctor_set_uint8(v___x_3163_, 8, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 9, v___x_3160_);
lean_ctor_set_uint8(v___x_3163_, 10, v___x_3161_);
lean_ctor_set_uint8(v___x_3163_, 11, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 12, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 13, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 14, v___x_3162_);
lean_ctor_set_uint8(v___x_3163_, 15, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 16, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 17, v___x_3069_);
lean_ctor_set_uint8(v___x_3163_, 18, v___x_3069_);
v___x_3164_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3163_);
v___x_3165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set_uint64(v___x_3165_, sizeof(void*)*1, v___x_3164_);
v___x_3166_ = lean_box(1);
v___x_3167_ = lean_unsigned_to_nat(0u);
v___x_3168_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3170_ = lean_box(0);
v___x_3171_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3171_, 0, v___x_3165_);
lean_ctor_set(v___x_3171_, 1, v___x_3166_);
lean_ctor_set(v___x_3171_, 2, v___x_3168_);
lean_ctor_set(v___x_3171_, 3, v___x_3169_);
lean_ctor_set(v___x_3171_, 4, v___x_3170_);
lean_ctor_set(v___x_3171_, 5, v___x_3167_);
lean_ctor_set(v___x_3171_, 6, v___x_3170_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*7, v___x_3159_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*7 + 1, v___x_3159_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*7 + 2, v___x_3159_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*7 + 3, v___x_3069_);
v___x_3172_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3173_ = lean_st_mk_ref(v___x_3172_);
v___x_3174_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3127_, v___x_3171_, v___x_3173_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___x_3171_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref(v___x_3174_);
v___x_3176_ = lean_st_ref_get(v___x_3173_);
lean_dec(v___x_3173_);
lean_dec(v___x_3176_);
v___y_3048_ = v___x_3069_;
v___y_3049_ = v___x_3122_;
v___y_3050_ = v_a_3067_;
v_a_3051_ = v_a_3175_;
goto v___jp_3047_;
}
else
{
lean_dec(v___x_3173_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3177_; 
v_a_3177_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3177_);
lean_dec_ref(v___x_3174_);
v___y_3048_ = v___x_3069_;
v___y_3049_ = v___x_3122_;
v___y_3050_ = v_a_3067_;
v_a_3051_ = v_a_3177_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3178_; 
v_a_3178_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3174_);
v___y_3054_ = v___x_3122_;
v___y_3055_ = v_a_3067_;
v_a_3056_ = v_a_3178_;
goto v___jp_3053_;
}
}
}
}
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_dec(v___x_3125_);
lean_dec(v_name_2870_);
v___x_3179_ = lean_box(0);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_3180_ = lean_apply_4(v___f_2869_, v___x_3179_, v___y_2871_, v___y_2872_, lean_box(0));
v___y_3059_ = v___x_3122_;
v___y_3060_ = v_a_3067_;
v___y_3061_ = v___x_3180_;
goto v___jp_3058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3288_, lean_object* v_name_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3288_, v_name_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
return v_res_3293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = lean_unsigned_to_nat(3137104340u);
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3339_ = l_Lean_Name_num___override(v___x_3338_, v___x_3337_);
return v___x_3339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3342_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3343_ = l_Lean_Name_str___override(v___x_3342_, v___x_3341_);
return v___x_3343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3346_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3347_ = l_Lean_Name_str___override(v___x_3346_, v___x_3345_);
return v___x_3347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_unsigned_to_nat(2u);
v___x_3349_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3350_ = l_Lean_Name_num___override(v___x_3349_, v___x_3348_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3352_; lean_object* v___x_3353_; 
v___f_3352_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3353_ = l_Lean_registerReservedNameAction(v___f_3352_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec_ref(v___x_3353_);
v___x_3354_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_3355_ = 0;
v___x_3356_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3357_ = l_Lean_registerTraceClass(v___x_3354_, v___x_3355_, v___x_3356_);
return v___x_3357_;
}
else
{
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b1_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_3361_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_00_u03b1_3366_, lean_object* v_x_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b1_3366_, v_x_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
return v_res_3371_;
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
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_eqns_nonrecursive = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_eqns_nonrecursive);
lean_dec_ref(res);
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_();
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
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
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
