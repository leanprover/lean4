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
lean_object* v_head_144_; lean_object* v_tail_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___y_149_; uint8_t v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_head_144_ = lean_ctor_get(v_as_x27_142_, 0);
v_tail_145_ = lean_ctor_get(v_as_x27_142_, 1);
v___x_146_ = lean_box(0);
v___x_147_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_155_ = 0;
lean_inc_ref(v_env_141_);
v___x_156_ = l_Lean_Environment_setExporting(v_env_141_, v___x_155_);
lean_inc(v_head_144_);
v___x_157_ = l_Lean_Environment_isSafeDefinition(v___x_156_, v_head_144_);
if (v___x_157_ == 0)
{
v___y_149_ = v___x_157_;
goto v___jp_148_;
}
else
{
uint8_t v___x_158_; 
lean_inc(v_head_144_);
lean_inc_ref(v_env_141_);
v___x_158_ = lean_is_matcher(v_env_141_, v_head_144_);
if (v___x_158_ == 0)
{
v___y_149_ = v___x_157_;
goto v___jp_148_;
}
else
{
v_as_x27_142_ = v_tail_145_;
v_b_143_ = v___x_147_;
goto _start;
}
}
v___jp_148_:
{
if (v___y_149_ == 0)
{
v_as_x27_142_ = v_tail_145_;
v_b_143_ = v___x_147_;
goto _start;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v_env_141_);
lean_inc(v_head_144_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_head_144_);
lean_ctor_set(v___x_151_, 1, v_str_140_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_146_);
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_160_, lean_object* v_env_161_, lean_object* v_as_x27_162_, lean_object* v_b_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_160_, v_env_161_, v_as_x27_162_, v_b_163_);
lean_dec_ref(v_b_163_);
lean_dec(v_as_x27_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_165_, lean_object* v_name_166_){
_start:
{
if (lean_obj_tag(v_name_166_) == 1)
{
lean_object* v_pre_167_; lean_object* v_str_168_; uint8_t v___x_169_; 
v_pre_167_ = lean_ctor_get(v_name_166_, 0);
lean_inc(v_pre_167_);
v_str_168_ = lean_ctor_get(v_name_166_, 1);
lean_inc_ref_n(v_str_168_, 2);
lean_dec_ref(v_name_166_);
v___x_169_ = l_Lean_Meta_isEqnLikeSuffix(v_str_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec_ref(v_str_168_);
lean_dec(v_pre_167_);
lean_dec_ref(v_env_165_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_fst_178_; 
lean_inc(v_pre_167_);
v___x_171_ = l_Lean_privateToUserName(v_pre_167_);
v___x_172_ = lean_box(0);
v___x_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v_pre_167_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_box(0);
v___x_176_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_177_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_168_, v_env_165_, v___x_174_, v___x_176_);
lean_dec_ref(v___x_174_);
v_fst_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_fst_178_);
lean_dec_ref(v___x_177_);
if (lean_obj_tag(v_fst_178_) == 0)
{
return v___x_175_;
}
else
{
lean_object* v_val_179_; 
v_val_179_ = lean_ctor_get(v_fst_178_, 0);
lean_inc(v_val_179_);
lean_dec_ref(v_fst_178_);
return v_val_179_;
}
}
}
else
{
lean_object* v___x_180_; 
lean_dec(v_name_166_);
lean_dec_ref(v_env_165_);
v___x_180_ = lean_box(0);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_181_, lean_object* v_env_182_, lean_object* v_as_183_, lean_object* v_as_x27_184_, lean_object* v_b_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_181_, v_env_182_, v_as_x27_184_, v_b_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_188_, lean_object* v_env_189_, lean_object* v_as_190_, lean_object* v_as_x27_191_, lean_object* v_b_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_188_, v_env_189_, v_as_190_, v_as_x27_191_, v_b_192_, v_a_193_);
lean_dec_ref(v_b_192_);
lean_dec(v_as_x27_191_);
lean_dec(v_as_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_195_, lean_object* v_declName_196_, lean_object* v_suffix_197_){
_start:
{
lean_object* v___x_201_; uint8_t v_isModule_202_; 
v___x_201_ = l_Lean_Environment_header(v_env_195_);
v_isModule_202_ = lean_ctor_get_uint8(v___x_201_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_201_);
if (v_isModule_202_ == 0)
{
lean_object* v_name_203_; 
lean_dec_ref(v_env_195_);
v_name_203_ = l_Lean_Name_str___override(v_declName_196_, v_suffix_197_);
return v_name_203_;
}
else
{
uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = 0;
lean_inc_ref(v_env_195_);
v___x_205_ = l_Lean_Environment_setExporting(v_env_195_, v_isModule_202_);
lean_inc(v_declName_196_);
v___x_206_ = l_Lean_Environment_find_x3f(v___x_205_, v_declName_196_, v___x_204_);
if (lean_obj_tag(v___x_206_) == 0)
{
goto v___jp_198_;
}
else
{
lean_object* v_val_207_; uint8_t v___x_208_; 
v_val_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_val_207_);
lean_dec_ref(v___x_206_);
v___x_208_ = l_Lean_ConstantInfo_hasValue(v_val_207_, v___x_204_);
lean_dec(v_val_207_);
if (v___x_208_ == 0)
{
goto v___jp_198_;
}
else
{
lean_object* v_name_209_; 
lean_dec_ref(v_env_195_);
v_name_209_ = l_Lean_Name_str___override(v_declName_196_, v_suffix_197_);
return v_name_209_;
}
}
}
v___jp_198_:
{
lean_object* v_name_199_; lean_object* v___x_200_; 
v_name_199_ = l_Lean_Name_str___override(v_declName_196_, v_suffix_197_);
v___x_200_ = l_Lean_mkPrivateName(v_env_195_, v_name_199_);
lean_dec_ref(v_env_195_);
return v___x_200_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v___x_214_);
lean_ctor_set(v___x_215_, 3, v___x_214_);
lean_ctor_set(v___x_215_, 4, v___x_213_);
lean_ctor_set(v___x_215_, 5, v___x_213_);
lean_ctor_set(v___x_215_, 6, v___x_213_);
lean_ctor_set(v___x_215_, 7, v___x_213_);
lean_ctor_set(v___x_215_, 8, v___x_213_);
lean_ctor_set(v___x_215_, 9, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(32u);
v___x_217_ = lean_mk_empty_array_with_capacity(v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = ((size_t)5ULL);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_unsigned_to_nat(32u);
v___x_222_ = lean_mk_empty_array_with_capacity(v___x_221_);
v___x_223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_224_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
lean_ctor_set(v___x_224_, 2, v___x_220_);
lean_ctor_set(v___x_224_, 3, v___x_220_);
lean_ctor_set_usize(v___x_224_, 4, v___x_219_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_225_ = lean_box(1);
v___x_226_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_227_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_225_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_env_234_; lean_object* v_options_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_233_ = lean_st_ref_get(v___y_231_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_env_234_);
lean_dec(v___x_233_);
v_options_235_ = lean_ctor_get(v___y_230_, 2);
v___x_236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_237_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_235_);
v___x_238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_238_, 0, v_env_234_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
lean_ctor_set(v___x_238_, 3, v_options_235_);
v___x_239_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_msgData_229_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_ref_250_; lean_object* v___x_251_; lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_260_; 
v_ref_250_ = lean_ctor_get(v___y_247_, 5);
v___x_251_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_246_, v___y_247_, v___y_248_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_260_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
lean_inc(v_ref_250_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_ref_250_);
lean_ctor_set(v___x_256_, 1, v_a_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v___x_256_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_265_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_268_ = l_Lean_stringToMessageData(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_271_ = l_Lean_stringToMessageData(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_275_, lean_object* v_reservedName_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_280_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_281_ = 0;
v___x_282_ = l_Lean_MessageData_ofConstName(v_declName_275_, v___x_281_);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_280_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = 1;
v___x_287_ = l_Lean_MessageData_ofConstName(v_reservedName_276_, v___x_286_);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_290_, v___y_277_, v___y_278_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_292_, lean_object* v_reservedName_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_292_, v_reservedName_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_298_, lean_object* v_suffix_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; lean_object* v_env_304_; lean_object* v_reservedName_305_; uint8_t v___x_306_; uint8_t v___x_307_; 
v___x_303_ = lean_st_ref_get(v___y_301_);
v_env_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref(v_env_304_);
lean_dec(v___x_303_);
lean_inc(v_declName_298_);
v_reservedName_305_ = l_Lean_Name_str___override(v_declName_298_, v_suffix_299_);
v___x_306_ = 1;
lean_inc(v_reservedName_305_);
v___x_307_ = l_Lean_Environment_contains(v_env_304_, v_reservedName_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_reservedName_305_);
lean_dec(v_declName_298_);
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_298_, v_reservedName_305_, v___y_300_, v___y_301_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_311_, lean_object* v_suffix_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_311_, v_suffix_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_317_);
v___x_322_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_317_, v___x_321_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v___x_322_);
v___x_323_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_317_);
v___x_324_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_317_, v___x_323_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec_ref(v___x_324_);
v___x_325_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_326_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_317_, v___x_325_, v_a_318_, v_a_319_);
return v___x_326_;
}
else
{
lean_dec(v_declName_317_);
return v___x_324_;
}
}
else
{
lean_dec(v_declName_317_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_332_, lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_333_, v___y_334_, v___y_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_338_, lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_338_, v_msg_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_343_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_344_, lean_object* v_n_345_){
_start:
{
lean_object* v___x_346_; 
lean_inc(v_n_345_);
lean_inc_ref(v_env_344_);
v___x_346_ = l_Lean_Meta_declFromEqLikeName(v_env_344_, v_n_345_);
if (lean_obj_tag(v___x_346_) == 1)
{
lean_object* v_val_347_; lean_object* v_fst_348_; lean_object* v_snd_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_val_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_val_347_);
lean_dec_ref(v___x_346_);
v_fst_348_ = lean_ctor_get(v_val_347_, 0);
lean_inc(v_fst_348_);
v_snd_349_ = lean_ctor_get(v_val_347_, 1);
lean_inc(v_snd_349_);
lean_dec(v_val_347_);
v___x_350_ = l_Lean_Meta_mkEqLikeNameFor(v_env_344_, v_fst_348_, v_snd_349_);
v___x_351_ = lean_name_eq(v_n_345_, v___x_350_);
lean_dec(v___x_350_);
lean_dec(v_n_345_);
return v___x_351_;
}
else
{
uint8_t v___x_352_; 
lean_dec(v___x_346_);
lean_dec(v_n_345_);
lean_dec_ref(v_env_344_);
v___x_352_ = 0;
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_353_, lean_object* v_n_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_353_, v_n_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_359_; lean_object* v___x_360_; 
v___f_359_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_360_ = l_Lean_registerReservedNamePredicate(v___f_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = lean_box(0);
v___x_365_ = lean_st_mk_ref(v___x_364_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_368_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_371_ = lean_mk_io_user_error(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_initializing();
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_391_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_391_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_391_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_391_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
uint8_t v___x_379_; 
v___x_379_ = lean_unbox(v_a_375_);
lean_dec(v_a_375_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_382_; 
lean_dec_ref(v_f_372_);
v___x_380_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 1);
lean_ctor_set(v___x_377_, 0, v___x_380_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_384_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_385_ = lean_st_ref_take(v___x_384_);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v_f_372_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_st_ref_set(v___x_384_, v___x_386_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_387_);
v___x_389_ = v___x_377_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v_f_372_);
v_a_392_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_374_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_374_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Meta_registerGetEqnsFn(v_f_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_413_; lean_object* v_env_414_; uint8_t v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_st_ref_get(v_a_407_);
v_env_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_ref(v_env_414_);
lean_dec(v___x_413_);
v___x_415_ = 0;
lean_inc(v_declName_403_);
v___x_416_ = l_Lean_Environment_findAsync_x3f(v_env_414_, v_declName_403_, v___x_415_);
if (lean_obj_tag(v___x_416_) == 1)
{
lean_object* v_val_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_448_; 
v_val_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_448_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_448_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_val_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_448_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
uint8_t v_kind_421_; 
v_kind_421_ = lean_ctor_get_uint8(v_val_417_, sizeof(void*)*3);
if (v_kind_421_ == 0)
{
lean_object* v_sig_422_; lean_object* v___x_423_; lean_object* v_env_424_; uint8_t v___x_425_; 
v_sig_422_ = lean_ctor_get(v_val_417_, 1);
lean_inc_ref(v_sig_422_);
lean_dec(v_val_417_);
v___x_423_ = lean_st_ref_get(v_a_407_);
v_env_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_env_424_);
lean_dec(v___x_423_);
v___x_425_ = lean_is_matcher(v_env_424_, v_declName_403_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v_type_427_; lean_object* v___x_428_; 
lean_del_object(v___x_419_);
v___x_426_ = lean_task_get_own(v_sig_422_);
v_type_427_ = lean_ctor_get(v___x_426_, 2);
lean_inc_ref(v_type_427_);
lean_dec(v___x_426_);
v___x_428_ = l_Lean_Meta_isProp(v_type_427_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_443_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_443_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint8_t v___x_433_; 
v___x_433_ = lean_unbox(v_a_429_);
lean_dec(v_a_429_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_434_ = 1;
v___x_435_ = lean_box(v___x_434_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_435_);
v___x_437_ = v___x_431_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = lean_box(v___x_425_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_439_);
v___x_441_ = v___x_431_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
return v___x_428_;
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_446_; 
lean_dec_ref(v_sig_422_);
v___x_444_ = lean_box(v___x_415_);
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 0);
lean_ctor_set(v___x_419_, 0, v___x_444_);
v___x_446_ = v___x_419_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_del_object(v___x_419_);
lean_dec(v_val_417_);
lean_dec(v_declName_403_);
goto v___jp_409_;
}
}
}
else
{
lean_dec(v___x_416_);
lean_dec(v_declName_403_);
goto v___jp_409_;
}
v___jp_409_:
{
uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = 0;
v___x_411_ = lean_box(v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_455_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_464_);
return v_res_466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_467_; lean_object* v___f_468_; 
v___x_467_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_468_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_468_, 0, v___x_467_);
return v___f_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___f_470_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_471_ = lean_box(0);
v___x_472_ = lean_box(1);
v___x_473_ = l_Lean_registerEnvExtension___redArg(v___f_470_, v___x_471_, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; lean_object* v_env_480_; lean_object* v_toConstantVal_481_; lean_object* v_value_482_; lean_object* v_all_483_; uint8_t v___y_485_; lean_object* v_type_493_; uint8_t v___x_494_; 
v___x_479_ = lean_st_ref_get(v___y_477_);
v_env_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref_n(v_env_480_, 2);
lean_dec(v___x_479_);
v_toConstantVal_481_ = lean_ctor_get(v_thm_476_, 0);
v_value_482_ = lean_ctor_get(v_thm_476_, 1);
v_all_483_ = lean_ctor_get(v_thm_476_, 2);
v_type_493_ = lean_ctor_get(v_toConstantVal_481_, 2);
v___x_494_ = l_Lean_Environment_hasUnsafe(v_env_480_, v_type_493_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Environment_hasUnsafe(v_env_480_, v_value_482_);
v___y_485_ = v___x_495_;
goto v___jp_484_;
}
else
{
lean_dec_ref(v_env_480_);
v___y_485_ = v___x_494_;
goto v___jp_484_;
}
v___jp_484_:
{
if (v___y_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_486_, 0, v_thm_476_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_inc(v_all_483_);
lean_inc_ref(v_value_482_);
lean_inc_ref(v_toConstantVal_481_);
lean_dec_ref(v_thm_476_);
v___x_488_ = lean_box(0);
v___x_489_ = 0;
v___x_490_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_490_, 0, v_toConstantVal_481_);
lean_ctor_set(v___x_490_, 1, v_value_482_);
lean_ctor_set(v___x_490_, 2, v___x_488_);
lean_ctor_set(v___x_490_, 3, v_all_483_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*4, v___x_489_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_496_, v___y_497_);
lean_dec(v___y_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_500_, v___y_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_514_, lean_object* v_b_515_, lean_object* v_c_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
v___x_522_ = lean_apply_7(v_k_514_, v_b_515_, v_c_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, lean_box(0));
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_523_, lean_object* v_b_524_, lean_object* v_c_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_523_, v_b_524_, v_c_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_532_, lean_object* v_k_533_, uint8_t v_cleanupAnnotations_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___f_540_; uint8_t v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_540_, 0, v_k_533_);
v___x_541_ = 1;
v___x_542_ = 0;
v___x_543_ = lean_box(0);
v___x_544_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_532_, v___x_541_, v___x_542_, v___x_541_, v___x_542_, v___x_543_, v___f_540_, v_cleanupAnnotations_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_544_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_544_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_561_, lean_object* v_k_562_, lean_object* v_cleanupAnnotations_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_569_; lean_object* v_res_570_; 
v_cleanupAnnotations_boxed_569_ = lean_unbox(v_cleanupAnnotations_563_);
v_res_570_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_561_, v_k_562_, v_cleanupAnnotations_boxed_569_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_571_, lean_object* v_e_572_, lean_object* v_k_573_, uint8_t v_cleanupAnnotations_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_572_, v_k_573_, v_cleanupAnnotations_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_581_, lean_object* v_e_582_, lean_object* v_k_583_, lean_object* v_cleanupAnnotations_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_590_; lean_object* v_res_591_; 
v_cleanupAnnotations_boxed_590_ = lean_unbox(v_cleanupAnnotations_584_);
v_res_591_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_581_, v_e_582_, v_k_583_, v_cleanupAnnotations_boxed_590_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
if (lean_obj_tag(v_a_592_) == 0)
{
lean_object* v___x_594_; 
v___x_594_ = l_List_reverse___redArg(v_a_593_);
return v___x_594_;
}
else
{
lean_object* v_head_595_; lean_object* v_tail_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
v_head_595_ = lean_ctor_get(v_a_592_, 0);
v_tail_596_ = lean_ctor_get(v_a_592_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_a_592_);
if (v_isSharedCheck_605_ == 0)
{
v___x_598_ = v_a_592_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_tail_596_);
lean_inc(v_head_595_);
lean_dec(v_a_592_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_mkLevelParam(v_head_595_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_a_593_);
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_593_);
v___x_602_ = v_reuseFailAlloc_604_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
v_a_592_ = v_tail_596_;
v_a_593_ = v___x_602_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_606_, lean_object* v_name_607_, lean_object* v_xs_608_, lean_object* v_body_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_name_615_; lean_object* v_levelParams_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_686_; 
v_name_615_ = lean_ctor_get(v_toConstantVal_606_, 0);
v_levelParams_616_ = lean_ctor_get(v_toConstantVal_606_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_toConstantVal_606_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_toConstantVal_606_, 2);
lean_dec(v_unused_687_);
v___x_618_ = v_toConstantVal_606_;
v_isShared_619_ = v_isSharedCheck_686_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_levelParams_616_);
lean_inc(v_name_615_);
lean_dec(v_toConstantVal_606_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_686_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_lhs_623_; lean_object* v___x_624_; 
v___x_620_ = lean_box(0);
lean_inc(v_levelParams_616_);
v___x_621_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_616_, v___x_620_);
v___x_622_ = l_Lean_mkConst(v_name_615_, v___x_621_);
v_lhs_623_ = l_Lean_mkAppN(v___x_622_, v_xs_608_);
lean_inc_ref(v_lhs_623_);
v___x_624_ = l_Lean_Meta_mkEq(v_lhs_623_, v_body_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; uint8_t v___x_626_; uint8_t v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref(v___x_624_);
v___x_626_ = 0;
v___x_627_ = 1;
v___x_628_ = 1;
v___x_629_ = l_Lean_Meta_mkForallFVars(v_xs_608_, v_a_625_, v___x_626_, v___x_627_, v___x_627_, v___x_628_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref(v___x_629_);
v___x_631_ = l_Lean_Meta_letToHave(v_a_630_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = l_Lean_Meta_mkEqRefl(v_lhs_623_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = l_Lean_Meta_mkLambdaFVars(v_xs_608_, v_a_634_, v___x_626_, v___x_627_, v___x_626_, v___x_627_, v___x_628_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
lean_inc(v_name_607_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 2, v_a_632_);
lean_ctor_set(v___x_618_, 0, v_name_607_);
v___x_638_ = v___x_618_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_name_607_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_levelParams_616_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_a_632_);
v___x_638_ = v_reuseFailAlloc_645_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_a_642_; lean_object* v___x_643_; 
lean_inc(v_name_607_);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v_name_607_);
lean_ctor_set(v___x_639_, 1, v___x_620_);
v___x_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v_a_636_);
lean_ctor_set(v___x_640_, 2, v___x_639_);
v___x_641_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_640_, v___y_613_);
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref(v___x_641_);
v___x_643_ = l_Lean_addDecl(v_a_642_, v___x_626_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_644_; 
lean_dec_ref(v___x_643_);
v___x_644_ = l_Lean_inferDefEqAttr(v_name_607_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
return v___x_644_;
}
else
{
lean_dec(v_name_607_);
return v___x_643_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_a_632_);
lean_del_object(v___x_618_);
lean_dec(v_levelParams_616_);
lean_dec(v_name_607_);
v_a_646_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_635_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_635_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_a_632_);
lean_del_object(v___x_618_);
lean_dec(v_levelParams_616_);
lean_dec(v_name_607_);
v_a_654_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_633_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_633_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_lhs_623_);
lean_del_object(v___x_618_);
lean_dec(v_levelParams_616_);
lean_dec(v_name_607_);
v_a_662_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_631_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_631_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_lhs_623_);
lean_del_object(v___x_618_);
lean_dec(v_levelParams_616_);
lean_dec(v_name_607_);
v_a_670_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_629_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_629_);
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
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v_lhs_623_);
lean_del_object(v___x_618_);
lean_dec(v_levelParams_616_);
lean_dec(v_name_607_);
v_a_678_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_624_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_624_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_688_, lean_object* v_name_689_, lean_object* v_xs_690_, lean_object* v_body_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_688_, v_name_689_, v_xs_690_, v_body_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_xs_690_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_698_, lean_object* v_info_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_toConstantVal_705_; lean_object* v_value_706_; lean_object* v___f_707_; uint8_t v___x_708_; lean_object* v___x_709_; 
v_toConstantVal_705_ = lean_ctor_get(v_info_699_, 0);
lean_inc_ref(v_toConstantVal_705_);
v_value_706_ = lean_ctor_get(v_info_699_, 1);
lean_inc_ref(v_value_706_);
lean_dec_ref(v_info_699_);
v___f_707_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_707_, 0, v_toConstantVal_705_);
lean_closure_set(v___f_707_, 1, v_name_698_);
v___x_708_ = 1;
v___x_709_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_706_, v___f_707_, v___x_708_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_710_, lean_object* v_info_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_710_, v_info_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_718_, lean_object* v_name_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_728_; lean_object* v_env_729_; uint8_t v___x_730_; lean_object* v___x_731_; 
v___x_728_ = lean_st_ref_get(v_a_723_);
v_env_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc_ref(v_env_729_);
lean_dec(v___x_728_);
v___x_730_ = 0;
lean_inc(v_declName_718_);
v___x_731_ = l_Lean_Environment_find_x3f(v_env_729_, v_declName_718_, v___x_730_);
if (lean_obj_tag(v___x_731_) == 1)
{
lean_object* v_val_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_758_; 
v_val_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_758_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_758_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_val_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_758_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
if (lean_obj_tag(v_val_732_) == 1)
{
lean_object* v_val_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_val_736_ = lean_ctor_get(v_val_732_, 0);
lean_inc_ref(v_val_736_);
lean_dec_ref(v_val_732_);
lean_inc_n(v_name_719_, 2);
v___x_737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_737_, 0, v_name_719_);
lean_closure_set(v___x_737_, 1, v_val_736_);
v___x_738_ = l_Lean_Meta_realizeConst(v_declName_718_, v_name_719_, v___x_737_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_748_; 
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v___x_738_, 0);
lean_dec(v_unused_749_);
v___x_740_ = v___x_738_;
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
else
{
lean_dec(v___x_738_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v_name_719_);
v___x_743_ = v___x_734_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_name_719_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_743_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
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
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_del_object(v___x_734_);
lean_dec(v_name_719_);
v_a_750_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_738_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_738_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_del_object(v___x_734_);
lean_dec(v_val_732_);
lean_dec(v_name_719_);
lean_dec(v_declName_718_);
goto v___jp_725_;
}
}
}
else
{
lean_dec(v___x_731_);
lean_dec(v_name_719_);
lean_dec(v_declName_718_);
goto v___jp_725_;
}
v___jp_725_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_759_, lean_object* v_name_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_mkSimpleEqThm(v_declName_759_, v_name_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_767_, lean_object* v_vals_768_, lean_object* v_i_769_, lean_object* v_k_770_){
_start:
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = lean_array_get_size(v_keys_767_);
v___x_772_ = lean_nat_dec_lt(v_i_769_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
lean_dec(v_i_769_);
v___x_773_ = lean_box(0);
return v___x_773_;
}
else
{
lean_object* v_k_x27_774_; uint8_t v___x_775_; 
v_k_x27_774_ = lean_array_fget_borrowed(v_keys_767_, v_i_769_);
v___x_775_ = lean_name_eq(v_k_770_, v_k_x27_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = lean_nat_add(v_i_769_, v___x_776_);
lean_dec(v_i_769_);
v_i_769_ = v___x_777_;
goto _start;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_array_fget_borrowed(v_vals_768_, v_i_769_);
lean_dec(v_i_769_);
lean_inc(v___x_779_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_781_, lean_object* v_vals_782_, lean_object* v_i_783_, lean_object* v_k_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_781_, v_vals_782_, v_i_783_, v_k_784_);
lean_dec(v_k_784_);
lean_dec_ref(v_vals_782_);
lean_dec_ref(v_keys_781_);
return v_res_785_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_786_; size_t v___x_787_; size_t v___x_788_; 
v___x_786_ = ((size_t)5ULL);
v___x_787_ = ((size_t)1ULL);
v___x_788_ = lean_usize_shift_left(v___x_787_, v___x_786_);
return v___x_788_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; 
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_791_ = lean_usize_sub(v___x_790_, v___x_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_792_, size_t v_x_793_, lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_object* v_es_795_; lean_object* v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v_j_800_; lean_object* v___x_801_; 
v_es_795_ = lean_ctor_get(v_x_792_, 0);
v___x_796_ = lean_box(2);
v___x_797_ = ((size_t)5ULL);
v___x_798_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_799_ = lean_usize_land(v_x_793_, v___x_798_);
v_j_800_ = lean_usize_to_nat(v___x_799_);
v___x_801_ = lean_array_get_borrowed(v___x_796_, v_es_795_, v_j_800_);
lean_dec(v_j_800_);
switch(lean_obj_tag(v___x_801_))
{
case 0:
{
lean_object* v_key_802_; lean_object* v_val_803_; uint8_t v___x_804_; 
v_key_802_ = lean_ctor_get(v___x_801_, 0);
v_val_803_ = lean_ctor_get(v___x_801_, 1);
v___x_804_ = lean_name_eq(v_x_794_, v_key_802_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_box(0);
return v___x_805_;
}
else
{
lean_object* v___x_806_; 
lean_inc(v_val_803_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_val_803_);
return v___x_806_;
}
}
case 1:
{
lean_object* v_node_807_; size_t v___x_808_; 
v_node_807_ = lean_ctor_get(v___x_801_, 0);
v___x_808_ = lean_usize_shift_right(v_x_793_, v___x_797_);
v_x_792_ = v_node_807_;
v_x_793_ = v___x_808_;
goto _start;
}
default: 
{
lean_object* v___x_810_; 
v___x_810_ = lean_box(0);
return v___x_810_;
}
}
}
else
{
lean_object* v_ks_811_; lean_object* v_vs_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_ks_811_ = lean_ctor_get(v_x_792_, 0);
v_vs_812_ = lean_ctor_get(v_x_792_, 1);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_811_, v_vs_812_, v___x_813_, v_x_794_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
size_t v_x_355__boxed_818_; lean_object* v_res_819_; 
v_x_355__boxed_818_ = lean_unbox_usize(v_x_816_);
lean_dec(v_x_816_);
v_res_819_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_815_, v_x_355__boxed_818_, v_x_817_);
lean_dec(v_x_817_);
lean_dec_ref(v_x_815_);
return v_res_819_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_820_; uint64_t v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(1723u);
v___x_821_ = lean_uint64_of_nat(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
uint64_t v___y_825_; 
if (lean_obj_tag(v_x_823_) == 0)
{
uint64_t v___x_828_; 
v___x_828_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_825_ = v___x_828_;
goto v___jp_824_;
}
else
{
uint64_t v_hash_829_; 
v_hash_829_ = lean_ctor_get_uint64(v_x_823_, sizeof(void*)*2);
v___y_825_ = v_hash_829_;
goto v___jp_824_;
}
v___jp_824_:
{
size_t v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_uint64_to_usize(v___y_825_);
v___x_827_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_822_, v___x_826_, v_x_823_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_830_, v_x_831_);
lean_dec(v_x_831_);
lean_dec_ref(v_x_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_836_; lean_object* v_env_837_; lean_object* v___x_838_; lean_object* v_asyncMode_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_836_ = lean_st_ref_get(v_a_834_);
v_env_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc_ref(v_env_837_);
lean_dec(v___x_836_);
v___x_838_ = l_Lean_Meta_eqnsExt;
v_asyncMode_839_ = lean_ctor_get(v___x_838_, 2);
v___x_840_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_841_ = lean_box(0);
v___x_842_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_840_, v___x_838_, v_env_837_, v_asyncMode_839_, v___x_841_);
v___x_843_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_842_, v_thmName_833_);
lean_dec(v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec(v_thmName_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_849_, v_a_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_thmName_854_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_863_, v_x_864_, v_x_865_);
lean_dec(v_x_865_);
lean_dec_ref(v_x_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, size_t v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_460__boxed_876_; lean_object* v_res_877_; 
v_x_460__boxed_876_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_res_877_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_872_, v_x_873_, v_x_460__boxed_876_, v_x_875_);
lean_dec(v_x_875_);
lean_dec_ref(v_x_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_878_, lean_object* v_keys_879_, lean_object* v_vals_880_, lean_object* v_heq_881_, lean_object* v_i_882_, lean_object* v_k_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_879_, v_vals_880_, v_i_882_, v_k_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_885_, lean_object* v_keys_886_, lean_object* v_vals_887_, lean_object* v_heq_888_, lean_object* v_i_889_, lean_object* v_k_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_885_, v_keys_886_, v_vals_887_, v_heq_888_, v_i_889_, v_k_890_);
lean_dec(v_k_890_);
lean_dec_ref(v_vals_887_);
lean_dec_ref(v_keys_886_);
return v_res_891_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_892_, lean_object* v_i_893_, lean_object* v_k_894_){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_array_get_size(v_keys_892_);
v___x_896_ = lean_nat_dec_lt(v_i_893_, v___x_895_);
if (v___x_896_ == 0)
{
lean_dec(v_i_893_);
return v___x_896_;
}
else
{
lean_object* v_k_x27_897_; uint8_t v___x_898_; 
v_k_x27_897_ = lean_array_fget_borrowed(v_keys_892_, v_i_893_);
v___x_898_ = lean_name_eq(v_k_894_, v_k_x27_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_add(v_i_893_, v___x_899_);
lean_dec(v_i_893_);
v_i_893_ = v___x_900_;
goto _start;
}
else
{
lean_dec(v_i_893_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_902_, lean_object* v_i_903_, lean_object* v_k_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_902_, v_i_903_, v_k_904_);
lean_dec(v_k_904_);
lean_dec_ref(v_keys_902_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_907_, size_t v_x_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_907_) == 0)
{
lean_object* v_es_910_; lean_object* v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v_j_915_; lean_object* v___x_916_; 
v_es_910_ = lean_ctor_get(v_x_907_, 0);
v___x_911_ = lean_box(2);
v___x_912_ = ((size_t)5ULL);
v___x_913_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_914_ = lean_usize_land(v_x_908_, v___x_913_);
v_j_915_ = lean_usize_to_nat(v___x_914_);
v___x_916_ = lean_array_get_borrowed(v___x_911_, v_es_910_, v_j_915_);
lean_dec(v_j_915_);
switch(lean_obj_tag(v___x_916_))
{
case 0:
{
lean_object* v_key_917_; uint8_t v___x_918_; 
v_key_917_ = lean_ctor_get(v___x_916_, 0);
v___x_918_ = lean_name_eq(v_x_909_, v_key_917_);
return v___x_918_;
}
case 1:
{
lean_object* v_node_919_; size_t v___x_920_; 
v_node_919_ = lean_ctor_get(v___x_916_, 0);
v___x_920_ = lean_usize_shift_right(v_x_908_, v___x_912_);
v_x_907_ = v_node_919_;
v_x_908_ = v___x_920_;
goto _start;
}
default: 
{
uint8_t v___x_922_; 
v___x_922_ = 0;
return v___x_922_;
}
}
}
else
{
lean_object* v_ks_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_ks_923_ = lean_ctor_get(v_x_907_, 0);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_923_, v___x_924_, v_x_909_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
size_t v_x_335__boxed_929_; uint8_t v_res_930_; lean_object* v_r_931_; 
v_x_335__boxed_929_ = lean_unbox_usize(v_x_927_);
lean_dec(v_x_927_);
v_res_930_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_926_, v_x_335__boxed_929_, v_x_928_);
lean_dec(v_x_928_);
lean_dec_ref(v_x_926_);
v_r_931_ = lean_box(v_res_930_);
return v_r_931_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
uint64_t v___y_935_; 
if (lean_obj_tag(v_x_933_) == 0)
{
uint64_t v___x_938_; 
v___x_938_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_935_ = v___x_938_;
goto v___jp_934_;
}
else
{
uint64_t v_hash_939_; 
v_hash_939_ = lean_ctor_get_uint64(v_x_933_, sizeof(void*)*2);
v___y_935_ = v_hash_939_;
goto v___jp_934_;
}
v___jp_934_:
{
size_t v___x_936_; uint8_t v___x_937_; 
v___x_936_ = lean_uint64_to_usize(v___y_935_);
v___x_937_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_932_, v___x_936_, v_x_933_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_940_, v_x_941_);
lean_dec(v_x_941_);
lean_dec_ref(v_x_940_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; lean_object* v_env_948_; lean_object* v___x_949_; lean_object* v_asyncMode_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_947_ = lean_st_ref_get(v_a_945_);
v_env_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc_ref(v_env_948_);
lean_dec(v___x_947_);
v___x_949_ = l_Lean_Meta_eqnsExt;
v_asyncMode_950_ = lean_ctor_get(v___x_949_, 2);
v___x_951_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_952_ = lean_box(0);
v___x_953_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_951_, v___x_949_, v_env_948_, v_asyncMode_950_, v___x_952_);
v___x_954_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_953_, v_thmName_944_);
lean_dec(v___x_953_);
v___x_955_ = lean_box(v___x_954_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec(v_thmName_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_961_, v_a_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Meta_isEqnThm(v_thmName_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_thmName_966_);
return v_res_970_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_971_, lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_972_, v_x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
uint8_t v_res_978_; lean_object* v_r_979_; 
v_res_978_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_975_, v_x_976_, v_x_977_);
lean_dec(v_x_977_);
lean_dec_ref(v_x_976_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, size_t v_x_982_, lean_object* v_x_983_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_981_, v_x_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
size_t v_x_429__boxed_989_; uint8_t v_res_990_; lean_object* v_r_991_; 
v_x_429__boxed_989_ = lean_unbox_usize(v_x_987_);
lean_dec(v_x_987_);
v_res_990_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_985_, v_x_986_, v_x_429__boxed_989_, v_x_988_);
lean_dec(v_x_988_);
lean_dec_ref(v_x_986_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_992_, lean_object* v_keys_993_, lean_object* v_vals_994_, lean_object* v_heq_995_, lean_object* v_i_996_, lean_object* v_k_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_993_, v_i_996_, v_k_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_999_, lean_object* v_keys_1000_, lean_object* v_vals_1001_, lean_object* v_heq_1002_, lean_object* v_i_1003_, lean_object* v_k_1004_){
_start:
{
uint8_t v_res_1005_; lean_object* v_r_1006_; 
v_res_1005_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_999_, v_keys_1000_, v_vals_1001_, v_heq_1002_, v_i_1003_, v_k_1004_);
lean_dec(v_k_1004_);
lean_dec_ref(v_vals_1001_);
lean_dec_ref(v_keys_1000_);
v_r_1006_ = lean_box(v_res_1005_);
return v_r_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v_ks_1011_; lean_object* v_vs_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1036_; 
v_ks_1011_ = lean_ctor_get(v_x_1007_, 0);
v_vs_1012_ = lean_ctor_get(v_x_1007_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1014_ = v_x_1007_;
v_isShared_1015_ = v_isSharedCheck_1036_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_vs_1012_);
lean_inc(v_ks_1011_);
lean_dec(v_x_1007_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1036_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_array_get_size(v_ks_1011_);
v___x_1017_ = lean_nat_dec_lt(v_x_1008_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_dec(v_x_1008_);
v___x_1018_ = lean_array_push(v_ks_1011_, v_x_1009_);
v___x_1019_ = lean_array_push(v_vs_1012_, v_x_1010_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1019_);
lean_ctor_set(v___x_1014_, 0, v___x_1018_);
v___x_1021_ = v___x_1014_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
else
{
lean_object* v_k_x27_1023_; uint8_t v___x_1024_; 
v_k_x27_1023_ = lean_array_fget_borrowed(v_ks_1011_, v_x_1008_);
v___x_1024_ = lean_name_eq(v_x_1009_, v_k_x27_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1026_; 
if (v_isShared_1015_ == 0)
{
v___x_1026_ = v___x_1014_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_ks_1011_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_vs_1012_);
v___x_1026_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_x_1008_, v___x_1027_);
lean_dec(v_x_1008_);
v_x_1007_ = v___x_1026_;
v_x_1008_ = v___x_1028_;
goto _start;
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1031_ = lean_array_fset(v_ks_1011_, v_x_1008_, v_x_1009_);
v___x_1032_ = lean_array_fset(v_vs_1012_, v_x_1008_, v_x_1010_);
lean_dec(v_x_1008_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1032_);
lean_ctor_set(v___x_1014_, 0, v___x_1031_);
v___x_1034_ = v___x_1014_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1037_, lean_object* v_k_1038_, lean_object* v_v_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1037_, v___x_1040_, v_k_1038_, v_v_1039_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1043_, size_t v_x_1044_, size_t v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_object* v_es_1048_; size_t v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; size_t v___x_1052_; lean_object* v_j_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_es_1048_ = lean_ctor_get(v_x_1043_, 0);
v___x_1049_ = ((size_t)5ULL);
v___x_1050_ = ((size_t)1ULL);
v___x_1051_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1052_ = lean_usize_land(v_x_1044_, v___x_1051_);
v_j_1053_ = lean_usize_to_nat(v___x_1052_);
v___x_1054_ = lean_array_get_size(v_es_1048_);
v___x_1055_ = lean_nat_dec_lt(v_j_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_dec(v_j_1053_);
lean_dec(v_x_1047_);
lean_dec(v_x_1046_);
return v_x_1043_;
}
else
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1092_; 
lean_inc_ref(v_es_1048_);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v_x_1043_, 0);
lean_dec(v_unused_1093_);
v___x_1057_ = v_x_1043_;
v_isShared_1058_ = v_isSharedCheck_1092_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v_x_1043_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1092_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_v_1059_; lean_object* v___x_1060_; lean_object* v_xs_x27_1061_; lean_object* v___y_1063_; 
v_v_1059_ = lean_array_fget(v_es_1048_, v_j_1053_);
v___x_1060_ = lean_box(0);
v_xs_x27_1061_ = lean_array_fset(v_es_1048_, v_j_1053_, v___x_1060_);
switch(lean_obj_tag(v_v_1059_))
{
case 0:
{
lean_object* v_key_1068_; lean_object* v_val_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1079_; 
v_key_1068_ = lean_ctor_get(v_v_1059_, 0);
v_val_1069_ = lean_ctor_get(v_v_1059_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_v_1059_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1071_ = v_v_1059_;
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_val_1069_);
lean_inc(v_key_1068_);
lean_dec(v_v_1059_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_name_eq(v_x_1046_, v_key_1068_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_del_object(v___x_1071_);
v___x_1074_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1068_, v_val_1069_, v_x_1046_, v_x_1047_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
v___y_1063_ = v___x_1075_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_val_1069_);
lean_dec(v_key_1068_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_x_1047_);
lean_ctor_set(v___x_1071_, 0, v_x_1046_);
v___x_1077_ = v___x_1071_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_x_1046_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_x_1047_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
v___y_1063_ = v___x_1077_;
goto v___jp_1062_;
}
}
}
}
case 1:
{
lean_object* v_node_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1090_; 
v_node_1080_ = lean_ctor_get(v_v_1059_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_v_1059_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1082_ = v_v_1059_;
v_isShared_1083_ = v_isSharedCheck_1090_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_node_1080_);
lean_dec(v_v_1059_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1090_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1084_ = lean_usize_shift_right(v_x_1044_, v___x_1049_);
v___x_1085_ = lean_usize_add(v_x_1045_, v___x_1050_);
v___x_1086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1080_, v___x_1084_, v___x_1085_, v_x_1046_, v_x_1047_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1086_);
v___x_1088_ = v___x_1082_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v___y_1063_ = v___x_1088_;
goto v___jp_1062_;
}
}
}
default: 
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_x_1046_);
lean_ctor_set(v___x_1091_, 1, v_x_1047_);
v___y_1063_ = v___x_1091_;
goto v___jp_1062_;
}
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_array_fset(v_xs_x27_1061_, v_j_1053_, v___y_1063_);
lean_dec(v_j_1053_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1064_);
v___x_1066_ = v___x_1057_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
else
{
lean_object* v_ks_1094_; lean_object* v_vs_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1115_; 
v_ks_1094_ = lean_ctor_get(v_x_1043_, 0);
v_vs_1095_ = lean_ctor_get(v_x_1043_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1097_ = v_x_1043_;
v_isShared_1098_ = v_isSharedCheck_1115_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_vs_1095_);
lean_inc(v_ks_1094_);
lean_dec(v_x_1043_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1115_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_ks_1094_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_vs_1095_);
v___x_1100_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v_newNode_1101_; uint8_t v___y_1103_; size_t v___x_1109_; uint8_t v___x_1110_; 
v_newNode_1101_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1100_, v_x_1046_, v_x_1047_);
v___x_1109_ = ((size_t)7ULL);
v___x_1110_ = lean_usize_dec_le(v___x_1109_, v_x_1045_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1101_);
v___x_1112_ = lean_unsigned_to_nat(4u);
v___x_1113_ = lean_nat_dec_lt(v___x_1111_, v___x_1112_);
lean_dec(v___x_1111_);
v___y_1103_ = v___x_1113_;
goto v___jp_1102_;
}
else
{
v___y_1103_ = v___x_1110_;
goto v___jp_1102_;
}
v___jp_1102_:
{
if (v___y_1103_ == 0)
{
lean_object* v_ks_1104_; lean_object* v_vs_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_ks_1104_ = lean_ctor_get(v_newNode_1101_, 0);
lean_inc_ref(v_ks_1104_);
v_vs_1105_ = lean_ctor_get(v_newNode_1101_, 1);
lean_inc_ref(v_vs_1105_);
lean_dec_ref(v_newNode_1101_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1045_, v_ks_1104_, v_vs_1105_, v___x_1106_, v___x_1107_);
lean_dec_ref(v_vs_1105_);
lean_dec_ref(v_ks_1104_);
return v___x_1108_;
}
else
{
return v_newNode_1101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1116_, lean_object* v_keys_1117_, lean_object* v_vals_1118_, lean_object* v_i_1119_, lean_object* v_entries_1120_){
_start:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_array_get_size(v_keys_1117_);
v___x_1122_ = lean_nat_dec_lt(v_i_1119_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_dec(v_i_1119_);
return v_entries_1120_;
}
else
{
lean_object* v_k_1123_; lean_object* v_v_1124_; uint64_t v___y_1126_; 
v_k_1123_ = lean_array_fget_borrowed(v_keys_1117_, v_i_1119_);
v_v_1124_ = lean_array_fget_borrowed(v_vals_1118_, v_i_1119_);
if (lean_obj_tag(v_k_1123_) == 0)
{
uint64_t v___x_1137_; 
v___x_1137_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1126_ = v___x_1137_;
goto v___jp_1125_;
}
else
{
uint64_t v_hash_1138_; 
v_hash_1138_ = lean_ctor_get_uint64(v_k_1123_, sizeof(void*)*2);
v___y_1126_ = v_hash_1138_;
goto v___jp_1125_;
}
v___jp_1125_:
{
size_t v_h_1127_; size_t v___x_1128_; lean_object* v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; size_t v_h_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_h_1127_ = lean_uint64_to_usize(v___y_1126_);
v___x_1128_ = ((size_t)5ULL);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_sub(v_depth_1116_, v___x_1130_);
v___x_1132_ = lean_usize_mul(v___x_1128_, v___x_1131_);
v_h_1133_ = lean_usize_shift_right(v_h_1127_, v___x_1132_);
v___x_1134_ = lean_nat_add(v_i_1119_, v___x_1129_);
lean_dec(v_i_1119_);
lean_inc(v_v_1124_);
lean_inc(v_k_1123_);
v___x_1135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1120_, v_h_1133_, v_depth_1116_, v_k_1123_, v_v_1124_);
v_i_1119_ = v___x_1134_;
v_entries_1120_ = v___x_1135_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1139_, lean_object* v_keys_1140_, lean_object* v_vals_1141_, lean_object* v_i_1142_, lean_object* v_entries_1143_){
_start:
{
size_t v_depth_boxed_1144_; lean_object* v_res_1145_; 
v_depth_boxed_1144_ = lean_unbox_usize(v_depth_1139_);
lean_dec(v_depth_1139_);
v_res_1145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1144_, v_keys_1140_, v_vals_1141_, v_i_1142_, v_entries_1143_);
lean_dec_ref(v_vals_1141_);
lean_dec_ref(v_keys_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
size_t v_x_634__boxed_1151_; size_t v_x_635__boxed_1152_; lean_object* v_res_1153_; 
v_x_634__boxed_1151_ = lean_unbox_usize(v_x_1147_);
lean_dec(v_x_1147_);
v_x_635__boxed_1152_ = lean_unbox_usize(v_x_1148_);
lean_dec(v_x_1148_);
v_res_1153_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1146_, v_x_634__boxed_1151_, v_x_635__boxed_1152_, v_x_1149_, v_x_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
uint64_t v___y_1158_; 
if (lean_obj_tag(v_x_1155_) == 0)
{
uint64_t v___x_1162_; 
v___x_1162_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1158_ = v___x_1162_;
goto v___jp_1157_;
}
else
{
uint64_t v_hash_1163_; 
v_hash_1163_ = lean_ctor_get_uint64(v_x_1155_, sizeof(void*)*2);
v___y_1158_ = v_hash_1163_;
goto v___jp_1157_;
}
v___jp_1157_:
{
size_t v___x_1159_; size_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_uint64_to_usize(v___y_1158_);
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1154_, v___x_1159_, v___x_1160_, v_x_1155_, v_x_1156_);
return v___x_1161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1164_, lean_object* v_as_1165_, size_t v_i_1166_, size_t v_stop_1167_, lean_object* v_b_1168_){
_start:
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_usize_dec_eq(v_i_1166_, v_stop_1167_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; 
v___x_1170_ = lean_array_uget_borrowed(v_as_1165_, v_i_1166_);
lean_inc(v_declName_1164_);
lean_inc(v___x_1170_);
v___x_1171_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1168_, v___x_1170_, v_declName_1164_);
v___x_1172_ = ((size_t)1ULL);
v___x_1173_ = lean_usize_add(v_i_1166_, v___x_1172_);
v_i_1166_ = v___x_1173_;
v_b_1168_ = v___x_1171_;
goto _start;
}
else
{
lean_dec(v_declName_1164_);
return v_b_1168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1175_, lean_object* v_as_1176_, lean_object* v_i_1177_, lean_object* v_stop_1178_, lean_object* v_b_1179_){
_start:
{
size_t v_i_boxed_1180_; size_t v_stop_boxed_1181_; lean_object* v_res_1182_; 
v_i_boxed_1180_ = lean_unbox_usize(v_i_1177_);
lean_dec(v_i_1177_);
v_stop_boxed_1181_ = lean_unbox_usize(v_stop_1178_);
lean_dec(v_stop_1178_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1175_, v_as_1176_, v_i_boxed_1180_, v_stop_boxed_1181_, v_b_1179_);
lean_dec_ref(v_as_1176_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1183_, lean_object* v_declName_1184_, lean_object* v_s_1185_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_array_get_size(v_eqThms_1183_);
v___x_1188_ = lean_nat_dec_lt(v___x_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_dec(v_declName_1184_);
return v_s_1185_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_nat_dec_le(v___x_1187_, v___x_1187_);
if (v___x_1189_ == 0)
{
if (v___x_1188_ == 0)
{
lean_dec(v_declName_1184_);
return v_s_1185_;
}
else
{
size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = ((size_t)0ULL);
v___x_1191_ = lean_usize_of_nat(v___x_1187_);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1184_, v_eqThms_1183_, v___x_1190_, v___x_1191_, v_s_1185_);
return v___x_1192_;
}
}
else
{
size_t v___x_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = lean_usize_of_nat(v___x_1187_);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1184_, v_eqThms_1183_, v___x_1193_, v___x_1194_, v_s_1185_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1196_, lean_object* v_declName_1197_, lean_object* v_s_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1196_, v_declName_1197_, v_s_1198_);
lean_dec_ref(v_eqThms_1196_);
return v_res_1199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0(void){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__0);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1205_, lean_object* v_eqThms_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1209_; lean_object* v_env_1210_; lean_object* v_nextMacroScope_1211_; lean_object* v_ngen_1212_; lean_object* v_auxDeclNGen_1213_; lean_object* v_traceState_1214_; lean_object* v_messages_1215_; lean_object* v_infoState_1216_; lean_object* v_snapshotTasks_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1233_; 
v___x_1209_ = lean_st_ref_take(v_a_1207_);
v_env_1210_ = lean_ctor_get(v___x_1209_, 0);
v_nextMacroScope_1211_ = lean_ctor_get(v___x_1209_, 1);
v_ngen_1212_ = lean_ctor_get(v___x_1209_, 2);
v_auxDeclNGen_1213_ = lean_ctor_get(v___x_1209_, 3);
v_traceState_1214_ = lean_ctor_get(v___x_1209_, 4);
v_messages_1215_ = lean_ctor_get(v___x_1209_, 6);
v_infoState_1216_ = lean_ctor_get(v___x_1209_, 7);
v_snapshotTasks_1217_ = lean_ctor_get(v___x_1209_, 8);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v___x_1209_, 5);
lean_dec(v_unused_1234_);
v___x_1219_ = v___x_1209_;
v_isShared_1220_ = v_isSharedCheck_1233_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_snapshotTasks_1217_);
lean_inc(v_infoState_1216_);
lean_inc(v_messages_1215_);
lean_inc(v_traceState_1214_);
lean_inc(v_auxDeclNGen_1213_);
lean_inc(v_ngen_1212_);
lean_inc(v_nextMacroScope_1211_);
lean_inc(v_env_1210_);
lean_dec(v___x_1209_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1233_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v_asyncMode_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1221_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1222_ = lean_ctor_get(v___x_1221_, 2);
v___f_1223_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1223_, 0, v_eqThms_1206_);
lean_closure_set(v___f_1223_, 1, v_declName_1205_);
v___x_1224_ = lean_box(0);
v___x_1225_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1221_, v_env_1210_, v___f_1223_, v_asyncMode_1222_, v___x_1224_);
v___x_1226_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 5, v___x_1226_);
lean_ctor_set(v___x_1219_, 0, v___x_1225_);
v___x_1228_ = v___x_1219_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_nextMacroScope_1211_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_ngen_1212_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_auxDeclNGen_1213_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v_traceState_1214_);
lean_ctor_set(v_reuseFailAlloc_1232_, 5, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1232_, 6, v_messages_1215_);
lean_ctor_set(v_reuseFailAlloc_1232_, 7, v_infoState_1216_);
lean_ctor_set(v_reuseFailAlloc_1232_, 8, v_snapshotTasks_1217_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = lean_st_ref_set(v_a_1207_, v___x_1228_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1235_, lean_object* v_eqThms_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1235_, v_eqThms_1236_, v_a_1237_);
lean_dec(v_a_1237_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1240_, lean_object* v_eqThms_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1240_, v_eqThms_1241_, v_a_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1246_, lean_object* v_eqThms_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1246_, v_eqThms_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1253_, v_x_1254_, v_x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1257_, lean_object* v_x_1258_, size_t v_x_1259_, size_t v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1258_, v_x_1259_, v_x_1260_, v_x_1261_, v_x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
size_t v_x_912__boxed_1270_; size_t v_x_913__boxed_1271_; lean_object* v_res_1272_; 
v_x_912__boxed_1270_ = lean_unbox_usize(v_x_1266_);
lean_dec(v_x_1266_);
v_x_913__boxed_1271_ = lean_unbox_usize(v_x_1267_);
lean_dec(v_x_1267_);
v_res_1272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1264_, v_x_1265_, v_x_912__boxed_1270_, v_x_913__boxed_1271_, v_x_1268_, v_x_1269_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1273_, lean_object* v_n_1274_, lean_object* v_k_1275_, lean_object* v_v_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1274_, v_k_1275_, v_v_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1278_, size_t v_depth_1279_, lean_object* v_keys_1280_, lean_object* v_vals_1281_, lean_object* v_heq_1282_, lean_object* v_i_1283_, lean_object* v_entries_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1279_, v_keys_1280_, v_vals_1281_, v_i_1283_, v_entries_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1286_, lean_object* v_depth_1287_, lean_object* v_keys_1288_, lean_object* v_vals_1289_, lean_object* v_heq_1290_, lean_object* v_i_1291_, lean_object* v_entries_1292_){
_start:
{
size_t v_depth_boxed_1293_; lean_object* v_res_1294_; 
v_depth_boxed_1293_ = lean_unbox_usize(v_depth_1287_);
lean_dec(v_depth_1287_);
v_res_1294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1286_, v_depth_boxed_1293_, v_keys_1288_, v_vals_1289_, v_heq_1290_, v_i_1291_, v_entries_1292_);
lean_dec_ref(v_vals_1289_);
lean_dec_ref(v_keys_1288_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1296_, v_x_1297_, v_x_1298_, v_x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1301_, lean_object* v_env_1302_, lean_object* v_idx_1303_, lean_object* v_eqs_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_nextEq_1311_; uint8_t v___x_1312_; 
v___x_1306_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1307_ = lean_unsigned_to_nat(1u);
v___x_1308_ = lean_nat_add(v_idx_1303_, v___x_1307_);
lean_dec(v_idx_1303_);
lean_inc(v___x_1308_);
v___x_1309_ = l_Nat_reprFast(v___x_1308_);
v___x_1310_ = lean_string_append(v___x_1306_, v___x_1309_);
lean_dec_ref(v___x_1309_);
lean_inc(v_declName_1301_);
lean_inc_ref(v_env_1302_);
v_nextEq_1311_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1302_, v_declName_1301_, v___x_1310_);
v___x_1312_ = l_Lean_Environment_containsOnBranch(v_env_1302_, v_nextEq_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v_nextEq_1311_);
lean_dec(v___x_1308_);
lean_dec_ref(v_env_1302_);
lean_dec(v_declName_1301_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_eqs_1304_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_array_push(v_eqs_1304_, v_nextEq_1311_);
v_idx_1303_ = v___x_1308_;
v_eqs_1304_ = v___x_1314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1316_, lean_object* v_env_1317_, lean_object* v_idx_1318_, lean_object* v_eqs_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1316_, v_env_1317_, v_idx_1318_, v_eqs_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1322_, lean_object* v_env_1323_, lean_object* v_idx_1324_, lean_object* v_eqs_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1322_, v_env_1323_, v_idx_1324_, v_eqs_1325_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1332_, lean_object* v_env_1333_, lean_object* v_idx_1334_, lean_object* v_eqs_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1332_, v_env_1333_, v_idx_1334_, v_eqs_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v_env_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; uint8_t v___x_1350_; 
v___x_1345_ = lean_st_ref_get(v_a_1343_);
v_env_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc_ref_n(v_env_1346_, 3);
lean_dec(v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1342_);
v___x_1348_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1346_, v_declName_1342_, v___x_1347_);
v___x_1349_ = 1;
lean_inc(v___x_1348_);
v___x_1350_ = l_Lean_Environment_contains(v_env_1346_, v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_dec(v___x_1348_);
lean_dec_ref(v_env_1346_);
lean_dec(v_declName_1342_);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_mk_empty_array_with_capacity(v___x_1353_);
v___x_1355_ = lean_array_push(v___x_1354_, v___x_1348_);
lean_inc(v_declName_1342_);
v___x_1356_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1342_, v_env_1346_, v___x_1353_, v___x_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc_n(v_a_1357_, 2);
lean_dec_ref(v___x_1356_);
v___x_1358_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1342_, v_a_1357_, v_a_1343_);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v___x_1358_, 0);
lean_dec(v_unused_1367_);
v___x_1360_ = v___x_1358_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_dec(v___x_1358_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_a_1357_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_declName_1342_);
v_a_1368_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1356_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1356_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1376_, v_a_1377_);
lean_dec(v_a_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1380_, v_a_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1394_, lean_object* v_localInsts_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1394_, v_localInsts_1395_, v_x_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
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
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1402_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1402_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1419_, lean_object* v_localInsts_1420_, lean_object* v_x_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1419_, v_localInsts_1420_, v_x_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1428_, lean_object* v_lctx_1429_, lean_object* v_localInsts_1430_, lean_object* v_x_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1429_, v_localInsts_1430_, v_x_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1438_, lean_object* v_lctx_1439_, lean_object* v_localInsts_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1438_, v_lctx_1439_, v_localInsts_1440_, v_x_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1451_, lean_object* v_as_x27_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
if (lean_obj_tag(v_as_x27_1452_) == 0)
{
lean_object* v___x_1459_; 
lean_dec(v_declName_1451_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v_b_1453_);
return v___x_1459_;
}
else
{
lean_object* v_head_1460_; lean_object* v_tail_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_b_1453_);
v_head_1460_ = lean_ctor_get(v_as_x27_1452_, 0);
v_tail_1461_ = lean_ctor_get(v_as_x27_1452_, 1);
lean_inc(v_head_1460_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v_declName_1451_);
v___x_1462_ = lean_apply_6(v_head_1460_, v_declName_1451_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, lean_box(0));
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = lean_box(0);
if (lean_obj_tag(v_a_1463_) == 1)
{
lean_object* v_val_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1475_; 
v_val_1465_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_val_1465_);
v___x_1466_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1451_, v_val_1465_, v___y_1457_);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; 
v_unused_1476_ = lean_ctor_get(v___x_1466_, 0);
lean_dec(v_unused_1476_);
v___x_1468_ = v___x_1466_;
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v___x_1466_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1463_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1464_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1471_);
v___x_1473_ = v___x_1468_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_object* v___x_1477_; 
lean_dec(v_a_1463_);
v___x_1477_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1452_ = v_tail_1461_;
v_b_1453_ = v___x_1477_;
goto _start;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_declName_1451_);
v_a_1479_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1462_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1462_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1487_, lean_object* v_as_x27_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1487_, v_as_x27_1488_, v_b_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v_as_x27_1488_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
lean_inc(v_declName_1496_);
v___x_1502_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1540_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1540_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1540_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_unbox(v_a_1503_);
lean_dec(v_a_1503_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
lean_dec(v_declName_1496_);
v___x_1508_ = lean_box(0);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1508_);
v___x_1510_ = v___x_1505_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
else
{
lean_object* v___x_1512_; 
lean_del_object(v___x_1505_);
lean_inc(v_declName_1496_);
v___x_1512_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1496_, v___y_1500_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
if (lean_obj_tag(v_a_1513_) == 1)
{
lean_dec_ref(v_a_1513_);
lean_dec(v_declName_1496_);
return v___x_1512_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec_ref(v___x_1512_);
lean_dec(v_a_1513_);
v___x_1514_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1515_ = lean_st_ref_get(v___x_1514_);
v___x_1516_ = lean_box(0);
v___x_1517_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1518_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1496_, v___x_1515_, v___x_1517_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___x_1515_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1531_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1531_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1531_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v_fst_1523_; 
v_fst_1523_ = lean_ctor_get(v_a_1519_, 0);
lean_inc(v_fst_1523_);
lean_dec(v_a_1519_);
if (lean_obj_tag(v_fst_1523_) == 0)
{
lean_object* v___x_1525_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1516_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1516_);
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
lean_object* v_val_1527_; lean_object* v___x_1529_; 
v_val_1527_ = lean_ctor_get(v_fst_1523_, 0);
lean_inc(v_val_1527_);
lean_dec_ref(v_fst_1523_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v_val_1527_);
v___x_1529_ = v___x_1521_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_val_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_a_1532_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1518_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1518_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
else
{
lean_dec(v_declName_1496_);
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_declName_1496_);
v_a_1541_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1502_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1502_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1556_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1559_ = lean_box(1);
v___x_1560_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1561_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1560_);
lean_ctor_set(v___x_1562_, 2, v___x_1559_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___f_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___f_1571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1571_, 0, v_declName_1565_);
v___x_1572_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1573_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1574_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1572_, v___x_1573_, v___f_1571_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1582_, lean_object* v_as_1583_, lean_object* v_as_x27_1584_, lean_object* v_b_1585_, lean_object* v_a_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1582_, v_as_x27_1584_, v_b_1585_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1593_, lean_object* v_as_1594_, lean_object* v_as_x27_1595_, lean_object* v_b_1596_, lean_object* v_a_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1593_, v_as_1594_, v_as_x27_1595_, v_b_1596_, v_a_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v_as_x27_1595_);
lean_dec(v_as_1594_);
return v_res_1603_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(lean_object* v_opts_1604_, lean_object* v_opt_1605_){
_start:
{
lean_object* v_name_1606_; lean_object* v_defValue_1607_; lean_object* v_map_1608_; lean_object* v___x_1609_; 
v_name_1606_ = lean_ctor_get(v_opt_1605_, 0);
v_defValue_1607_ = lean_ctor_get(v_opt_1605_, 1);
v_map_1608_ = lean_ctor_get(v_opts_1604_, 0);
v___x_1609_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1608_, v_name_1606_);
if (lean_obj_tag(v___x_1609_) == 0)
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_unbox(v_defValue_1607_);
return v___x_1610_;
}
else
{
lean_object* v_val_1611_; 
v_val_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1611_);
lean_dec_ref(v___x_1609_);
if (lean_obj_tag(v_val_1611_) == 1)
{
uint8_t v_v_1612_; 
v_v_1612_ = lean_ctor_get_uint8(v_val_1611_, 0);
lean_dec_ref(v_val_1611_);
return v_v_1612_;
}
else
{
uint8_t v___x_1613_; 
lean_dec(v_val_1611_);
v___x_1613_ = lean_unbox(v_defValue_1607_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1___boxed(lean_object* v_opts_1614_, lean_object* v_opt_1615_){
_start:
{
uint8_t v_res_1616_; lean_object* v_r_1617_; 
v_res_1616_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_1614_, v_opt_1615_);
lean_dec_ref(v_opt_1615_);
lean_dec_ref(v_opts_1614_);
v_r_1617_ = lean_box(v_res_1616_);
return v_r_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(lean_object* v_opts_1618_, lean_object* v_opt_1619_){
_start:
{
lean_object* v_name_1620_; lean_object* v_defValue_1621_; lean_object* v_map_1622_; lean_object* v___x_1623_; 
v_name_1620_ = lean_ctor_get(v_opt_1619_, 0);
v_defValue_1621_ = lean_ctor_get(v_opt_1619_, 1);
v_map_1622_ = lean_ctor_get(v_opts_1618_, 0);
v___x_1623_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1622_, v_name_1620_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_inc(v_defValue_1621_);
return v_defValue_1621_;
}
else
{
lean_object* v_val_1624_; 
v_val_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref(v___x_1623_);
if (lean_obj_tag(v_val_1624_) == 3)
{
lean_object* v_v_1625_; 
v_v_1625_ = lean_ctor_get(v_val_1624_, 0);
lean_inc(v_v_1625_);
lean_dec_ref(v_val_1624_);
return v_v_1625_;
}
else
{
lean_dec(v_val_1624_);
lean_inc(v_defValue_1621_);
return v_defValue_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2___boxed(lean_object* v_opts_1626_, lean_object* v_opt_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_1626_, v_opt_1627_);
lean_dec_ref(v_opt_1627_);
lean_dec_ref(v_opts_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(lean_object* v_o_1632_, lean_object* v_k_1633_, uint8_t v_v_1634_){
_start:
{
lean_object* v_map_1635_; uint8_t v_hasTrace_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1650_; 
v_map_1635_ = lean_ctor_get(v_o_1632_, 0);
v_hasTrace_1636_ = lean_ctor_get_uint8(v_o_1632_, sizeof(void*)*1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_o_1632_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1638_ = v_o_1632_;
v_isShared_1639_ = v_isSharedCheck_1650_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_map_1635_);
lean_dec(v_o_1632_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1650_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1640_, 0, v_v_1634_);
lean_inc(v_k_1633_);
v___x_1641_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1633_, v___x_1640_, v_map_1635_);
if (v_hasTrace_1636_ == 0)
{
lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1643_ = l_Lean_Name_isPrefixOf(v___x_1642_, v_k_1633_);
lean_dec(v_k_1633_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1641_);
v___x_1645_ = v___x_1638_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1641_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*1, v___x_1643_);
return v___x_1645_;
}
}
else
{
lean_object* v___x_1648_; 
lean_dec(v_k_1633_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1641_);
v___x_1648_ = v___x_1638_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, sizeof(void*)*1, v_hasTrace_1636_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___boxed(lean_object* v_o_1651_, lean_object* v_k_1652_, lean_object* v_v_1653_){
_start:
{
uint8_t v_v_boxed_1654_; lean_object* v_res_1655_; 
v_v_boxed_1654_ = lean_unbox(v_v_1653_);
v_res_1655_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_o_1651_, v_k_1652_, v_v_boxed_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(lean_object* v_opts_1656_, lean_object* v_opt_1657_, uint8_t v_val_1658_){
_start:
{
lean_object* v_name_1659_; lean_object* v___x_1660_; 
v_name_1659_ = lean_ctor_get(v_opt_1657_, 0);
lean_inc(v_name_1659_);
lean_dec_ref(v_opt_1657_);
v___x_1660_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0(v_opts_1656_, v_name_1659_, v_val_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object* v_opts_1661_, lean_object* v_opt_1662_, lean_object* v_val_1663_){
_start:
{
uint8_t v_val_boxed_1664_; lean_object* v_res_1665_; 
v_val_boxed_1664_ = lean_unbox(v_val_1663_);
v_res_1665_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_opts_1661_, v_opt_1662_, v_val_boxed_1664_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(lean_object* v_as_1666_, size_t v_i_1667_, size_t v_stop_1668_, lean_object* v_b_1669_){
_start:
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_usize_dec_eq(v_i_1667_, v_stop_1668_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v_defValue_1672_; uint8_t v___x_1673_; lean_object* v___x_1674_; size_t v___x_1675_; size_t v___x_1676_; 
v___x_1671_ = lean_array_uget_borrowed(v_as_1666_, v_i_1667_);
v_defValue_1672_ = lean_ctor_get(v___x_1671_, 1);
v___x_1673_ = lean_unbox(v_defValue_1672_);
lean_inc(v___x_1671_);
v___x_1674_ = l_Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0(v_b_1669_, v___x_1671_, v___x_1673_);
v___x_1675_ = ((size_t)1ULL);
v___x_1676_ = lean_usize_add(v_i_1667_, v___x_1675_);
v_i_1667_ = v___x_1676_;
v_b_1669_ = v___x_1674_;
goto _start;
}
else
{
return v_b_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3___boxed(lean_object* v_as_1678_, lean_object* v_i_1679_, lean_object* v_stop_1680_, lean_object* v_b_1681_){
_start:
{
size_t v_i_boxed_1682_; size_t v_stop_boxed_1683_; lean_object* v_res_1684_; 
v_i_boxed_1682_ = lean_unbox_usize(v_i_1679_);
lean_dec(v_i_1679_);
v_stop_boxed_1683_ = lean_unbox_usize(v_stop_1680_);
lean_dec(v_stop_1680_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v_as_1678_, v_i_boxed_1682_, v_stop_boxed_1683_, v_b_1681_);
lean_dec_ref(v_as_1678_);
return v_res_1684_;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1686_ = lean_array_get_size(v___x_1685_);
return v___x_1686_;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1688_ = lean_nat_dec_le(v___x_1687_, v___x_1687_);
return v___x_1688_;
}
}
static size_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1689_; size_t v___x_1690_; 
v___x_1689_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1690_ = lean_usize_of_nat(v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object* v_declName_1691_, lean_object* v___x_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___y_1699_; uint8_t v___y_1700_; lean_object* v_fileName_1701_; lean_object* v_fileMap_1702_; lean_object* v_currRecDepth_1703_; lean_object* v_ref_1704_; lean_object* v_currNamespace_1705_; lean_object* v_openDecls_1706_; lean_object* v_initHeartbeats_1707_; lean_object* v_maxHeartbeats_1708_; lean_object* v_quotContext_1709_; lean_object* v_currMacroScope_1710_; lean_object* v_cancelTk_x3f_1711_; uint8_t v_suppressElabErrors_1712_; lean_object* v_inheritedTraceOptions_1713_; lean_object* v___y_1714_; lean_object* v___x_1719_; lean_object* v_fileName_1720_; lean_object* v_fileMap_1721_; lean_object* v_options_1722_; lean_object* v_currRecDepth_1723_; lean_object* v_ref_1724_; lean_object* v_currNamespace_1725_; lean_object* v_openDecls_1726_; lean_object* v_initHeartbeats_1727_; lean_object* v_maxHeartbeats_1728_; lean_object* v_quotContext_1729_; lean_object* v_currMacroScope_1730_; lean_object* v_cancelTk_x3f_1731_; uint8_t v_suppressElabErrors_1732_; lean_object* v_inheritedTraceOptions_1733_; lean_object* v___y_1735_; uint8_t v___y_1736_; uint8_t v___y_1737_; lean_object* v___y_1759_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1719_ = lean_st_ref_get(v___y_1696_);
v_fileName_1720_ = lean_ctor_get(v___y_1695_, 0);
v_fileMap_1721_ = lean_ctor_get(v___y_1695_, 1);
v_options_1722_ = lean_ctor_get(v___y_1695_, 2);
v_currRecDepth_1723_ = lean_ctor_get(v___y_1695_, 3);
v_ref_1724_ = lean_ctor_get(v___y_1695_, 5);
v_currNamespace_1725_ = lean_ctor_get(v___y_1695_, 6);
v_openDecls_1726_ = lean_ctor_get(v___y_1695_, 7);
v_initHeartbeats_1727_ = lean_ctor_get(v___y_1695_, 8);
v_maxHeartbeats_1728_ = lean_ctor_get(v___y_1695_, 9);
v_quotContext_1729_ = lean_ctor_get(v___y_1695_, 10);
v_currMacroScope_1730_ = lean_ctor_get(v___y_1695_, 11);
v_cancelTk_x3f_1731_ = lean_ctor_get(v___y_1695_, 12);
v_suppressElabErrors_1732_ = lean_ctor_get_uint8(v___y_1695_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1733_ = lean_ctor_get(v___y_1695_, 13);
v___x_1764_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1765_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1766_ = lean_nat_dec_lt(v___x_1692_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_inc_ref(v_options_1722_);
v___y_1759_ = v_options_1722_;
goto v___jp_1758_;
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_uint8_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1);
if (v___x_1767_ == 0)
{
if (v___x_1766_ == 0)
{
lean_inc_ref(v_options_1722_);
v___y_1759_ = v_options_1722_;
goto v___jp_1758_;
}
else
{
size_t v___x_1768_; size_t v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = ((size_t)0ULL);
v___x_1769_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
lean_inc_ref(v_options_1722_);
v___x_1770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1764_, v___x_1768_, v___x_1769_, v_options_1722_);
v___y_1759_ = v___x_1770_;
goto v___jp_1758_;
}
}
else
{
size_t v___x_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
lean_inc_ref(v_options_1722_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getEqnsFor_x3f_spec__3(v___x_1764_, v___x_1771_, v___x_1772_, v_options_1722_);
v___y_1759_ = v___x_1773_;
goto v___jp_1758_;
}
}
v___jp_1698_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = l_Lean_maxRecDepth;
v___x_1716_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v___y_1699_, v___x_1715_);
lean_inc_ref(v_inheritedTraceOptions_1713_);
lean_inc(v_cancelTk_x3f_1711_);
lean_inc(v_currMacroScope_1710_);
lean_inc(v_quotContext_1709_);
lean_inc(v_maxHeartbeats_1708_);
lean_inc(v_initHeartbeats_1707_);
lean_inc(v_openDecls_1706_);
lean_inc(v_currNamespace_1705_);
lean_inc(v_ref_1704_);
lean_inc(v_currRecDepth_1703_);
lean_inc_ref(v_fileMap_1702_);
lean_inc_ref(v_fileName_1701_);
v___x_1717_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1717_, 0, v_fileName_1701_);
lean_ctor_set(v___x_1717_, 1, v_fileMap_1702_);
lean_ctor_set(v___x_1717_, 2, v___y_1699_);
lean_ctor_set(v___x_1717_, 3, v_currRecDepth_1703_);
lean_ctor_set(v___x_1717_, 4, v___x_1716_);
lean_ctor_set(v___x_1717_, 5, v_ref_1704_);
lean_ctor_set(v___x_1717_, 6, v_currNamespace_1705_);
lean_ctor_set(v___x_1717_, 7, v_openDecls_1706_);
lean_ctor_set(v___x_1717_, 8, v_initHeartbeats_1707_);
lean_ctor_set(v___x_1717_, 9, v_maxHeartbeats_1708_);
lean_ctor_set(v___x_1717_, 10, v_quotContext_1709_);
lean_ctor_set(v___x_1717_, 11, v_currMacroScope_1710_);
lean_ctor_set(v___x_1717_, 12, v_cancelTk_x3f_1711_);
lean_ctor_set(v___x_1717_, 13, v_inheritedTraceOptions_1713_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*14, v___y_1700_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*14 + 1, v_suppressElabErrors_1712_);
v___x_1718_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1691_, v___y_1693_, v___y_1694_, v___x_1717_, v___y_1714_);
lean_dec_ref(v___x_1717_);
return v___x_1718_;
}
v___jp_1734_:
{
if (v___y_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v_env_1739_; lean_object* v_nextMacroScope_1740_; lean_object* v_ngen_1741_; lean_object* v_auxDeclNGen_1742_; lean_object* v_traceState_1743_; lean_object* v_messages_1744_; lean_object* v_infoState_1745_; lean_object* v_snapshotTasks_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1756_; 
v___x_1738_ = lean_st_ref_take(v___y_1696_);
v_env_1739_ = lean_ctor_get(v___x_1738_, 0);
v_nextMacroScope_1740_ = lean_ctor_get(v___x_1738_, 1);
v_ngen_1741_ = lean_ctor_get(v___x_1738_, 2);
v_auxDeclNGen_1742_ = lean_ctor_get(v___x_1738_, 3);
v_traceState_1743_ = lean_ctor_get(v___x_1738_, 4);
v_messages_1744_ = lean_ctor_get(v___x_1738_, 6);
v_infoState_1745_ = lean_ctor_get(v___x_1738_, 7);
v_snapshotTasks_1746_ = lean_ctor_get(v___x_1738_, 8);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v___x_1738_, 5);
lean_dec(v_unused_1757_);
v___x_1748_ = v___x_1738_;
v_isShared_1749_ = v_isSharedCheck_1756_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snapshotTasks_1746_);
lean_inc(v_infoState_1745_);
lean_inc(v_messages_1744_);
lean_inc(v_traceState_1743_);
lean_inc(v_auxDeclNGen_1742_);
lean_inc(v_ngen_1741_);
lean_inc(v_nextMacroScope_1740_);
lean_inc(v_env_1739_);
lean_dec(v___x_1738_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1756_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1750_ = l_Lean_Kernel_enableDiag(v_env_1739_, v___y_1736_);
v___x_1751_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 5, v___x_1751_);
lean_ctor_set(v___x_1748_, 0, v___x_1750_);
v___x_1753_ = v___x_1748_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_nextMacroScope_1740_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_ngen_1741_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_auxDeclNGen_1742_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_traceState_1743_);
lean_ctor_set(v_reuseFailAlloc_1755_, 5, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1755_, 6, v_messages_1744_);
lean_ctor_set(v_reuseFailAlloc_1755_, 7, v_infoState_1745_);
lean_ctor_set(v_reuseFailAlloc_1755_, 8, v_snapshotTasks_1746_);
v___x_1753_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_st_ref_set(v___y_1696_, v___x_1753_);
v___y_1699_ = v___y_1735_;
v___y_1700_ = v___y_1736_;
v_fileName_1701_ = v_fileName_1720_;
v_fileMap_1702_ = v_fileMap_1721_;
v_currRecDepth_1703_ = v_currRecDepth_1723_;
v_ref_1704_ = v_ref_1724_;
v_currNamespace_1705_ = v_currNamespace_1725_;
v_openDecls_1706_ = v_openDecls_1726_;
v_initHeartbeats_1707_ = v_initHeartbeats_1727_;
v_maxHeartbeats_1708_ = v_maxHeartbeats_1728_;
v_quotContext_1709_ = v_quotContext_1729_;
v_currMacroScope_1710_ = v_currMacroScope_1730_;
v_cancelTk_x3f_1711_ = v_cancelTk_x3f_1731_;
v_suppressElabErrors_1712_ = v_suppressElabErrors_1732_;
v_inheritedTraceOptions_1713_ = v_inheritedTraceOptions_1733_;
v___y_1714_ = v___y_1696_;
goto v___jp_1698_;
}
}
}
else
{
v___y_1699_ = v___y_1735_;
v___y_1700_ = v___y_1736_;
v_fileName_1701_ = v_fileName_1720_;
v_fileMap_1702_ = v_fileMap_1721_;
v_currRecDepth_1703_ = v_currRecDepth_1723_;
v_ref_1704_ = v_ref_1724_;
v_currNamespace_1705_ = v_currNamespace_1725_;
v_openDecls_1706_ = v_openDecls_1726_;
v_initHeartbeats_1707_ = v_initHeartbeats_1727_;
v_maxHeartbeats_1708_ = v_maxHeartbeats_1728_;
v_quotContext_1709_ = v_quotContext_1729_;
v_currMacroScope_1710_ = v_currMacroScope_1730_;
v_cancelTk_x3f_1711_ = v_cancelTk_x3f_1731_;
v_suppressElabErrors_1712_ = v_suppressElabErrors_1732_;
v_inheritedTraceOptions_1713_ = v_inheritedTraceOptions_1733_;
v___y_1714_ = v___y_1696_;
goto v___jp_1698_;
}
}
v___jp_1758_:
{
lean_object* v_env_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; uint8_t v___x_1763_; 
v_env_1760_ = lean_ctor_get(v___x_1719_, 0);
lean_inc_ref(v_env_1760_);
lean_dec(v___x_1719_);
v___x_1761_ = l_Lean_diagnostics;
v___x_1762_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___y_1759_, v___x_1761_);
v___x_1763_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1760_);
lean_dec_ref(v_env_1760_);
if (v___x_1763_ == 0)
{
if (v___x_1762_ == 0)
{
v___y_1699_ = v___y_1759_;
v___y_1700_ = v___x_1762_;
v_fileName_1701_ = v_fileName_1720_;
v_fileMap_1702_ = v_fileMap_1721_;
v_currRecDepth_1703_ = v_currRecDepth_1723_;
v_ref_1704_ = v_ref_1724_;
v_currNamespace_1705_ = v_currNamespace_1725_;
v_openDecls_1706_ = v_openDecls_1726_;
v_initHeartbeats_1707_ = v_initHeartbeats_1727_;
v_maxHeartbeats_1708_ = v_maxHeartbeats_1728_;
v_quotContext_1709_ = v_quotContext_1729_;
v_currMacroScope_1710_ = v_currMacroScope_1730_;
v_cancelTk_x3f_1711_ = v_cancelTk_x3f_1731_;
v_suppressElabErrors_1712_ = v_suppressElabErrors_1732_;
v_inheritedTraceOptions_1713_ = v_inheritedTraceOptions_1733_;
v___y_1714_ = v___y_1696_;
goto v___jp_1698_;
}
else
{
v___y_1735_ = v___y_1759_;
v___y_1736_ = v___x_1762_;
v___y_1737_ = v___x_1763_;
goto v___jp_1734_;
}
}
else
{
v___y_1735_ = v___y_1759_;
v___y_1736_ = v___x_1762_;
v___y_1737_ = v___x_1762_;
goto v___jp_1734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object* v_declName_1774_, lean_object* v___x_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Meta_getEqnsFor_x3f___lam__0(v_declName_1774_, v___x_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___x_1775_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1788_ = lean_unsigned_to_nat(32u);
v___x_1789_ = lean_mk_empty_array_with_capacity(v___x_1788_);
lean_dec_ref(v___x_1789_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___f_1791_ = lean_alloc_closure((void*)(l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1791_, 0, v_declName_1782_);
lean_closure_set(v___f_1791_, 1, v___x_1790_);
v___x_1792_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1793_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1794_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1792_, v___x_1793_, v___f_1791_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(lean_object* v_msgData_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v_env_1809_; lean_object* v___x_1810_; lean_object* v_mctx_1811_; lean_object* v_lctx_1812_; lean_object* v_options_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1808_ = lean_st_ref_get(v___y_1806_);
v_env_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc_ref(v_env_1809_);
lean_dec(v___x_1808_);
v___x_1810_ = lean_st_ref_get(v___y_1804_);
v_mctx_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc_ref(v_mctx_1811_);
lean_dec(v___x_1810_);
v_lctx_1812_ = lean_ctor_get(v___y_1803_, 2);
v_options_1813_ = lean_ctor_get(v___y_1805_, 2);
lean_inc_ref(v_options_1813_);
lean_inc_ref(v_lctx_1812_);
v___x_1814_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1814_, 0, v_env_1809_);
lean_ctor_set(v___x_1814_, 1, v_mctx_1811_);
lean_ctor_set(v___x_1814_, 2, v_lctx_1812_);
lean_ctor_set(v___x_1814_, 3, v_options_1813_);
v___x_1815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v_msgData_1802_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1___boxed(lean_object* v_msgData_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msgData_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1823_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1824_; double v___x_1825_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = lean_float_of_nat(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(lean_object* v_cls_1829_, lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_ref_1836_; lean_object* v___x_1837_; lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1882_; 
v_ref_1836_ = lean_ctor_get(v___y_1833_, 5);
v___x_1837_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msg_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1882_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1882_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v_traceState_1843_; lean_object* v_env_1844_; lean_object* v_nextMacroScope_1845_; lean_object* v_ngen_1846_; lean_object* v_auxDeclNGen_1847_; lean_object* v_cache_1848_; lean_object* v_messages_1849_; lean_object* v_infoState_1850_; lean_object* v_snapshotTasks_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1881_; 
v___x_1842_ = lean_st_ref_take(v___y_1834_);
v_traceState_1843_ = lean_ctor_get(v___x_1842_, 4);
v_env_1844_ = lean_ctor_get(v___x_1842_, 0);
v_nextMacroScope_1845_ = lean_ctor_get(v___x_1842_, 1);
v_ngen_1846_ = lean_ctor_get(v___x_1842_, 2);
v_auxDeclNGen_1847_ = lean_ctor_get(v___x_1842_, 3);
v_cache_1848_ = lean_ctor_get(v___x_1842_, 5);
v_messages_1849_ = lean_ctor_get(v___x_1842_, 6);
v_infoState_1850_ = lean_ctor_get(v___x_1842_, 7);
v_snapshotTasks_1851_ = lean_ctor_get(v___x_1842_, 8);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1853_ = v___x_1842_;
v_isShared_1854_ = v_isSharedCheck_1881_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_snapshotTasks_1851_);
lean_inc(v_infoState_1850_);
lean_inc(v_messages_1849_);
lean_inc(v_cache_1848_);
lean_inc(v_traceState_1843_);
lean_inc(v_auxDeclNGen_1847_);
lean_inc(v_ngen_1846_);
lean_inc(v_nextMacroScope_1845_);
lean_inc(v_env_1844_);
lean_dec(v___x_1842_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1881_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
uint64_t v_tid_1855_; lean_object* v_traces_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1880_; 
v_tid_1855_ = lean_ctor_get_uint64(v_traceState_1843_, sizeof(void*)*1);
v_traces_1856_ = lean_ctor_get(v_traceState_1843_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_traceState_1843_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1858_ = v_traceState_1843_;
v_isShared_1859_ = v_isSharedCheck_1880_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_traces_1856_);
lean_dec(v_traceState_1843_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1880_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; double v___x_1861_; uint8_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0);
v___x_1862_ = 0;
v___x_1863_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1));
v___x_1864_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1864_, 0, v_cls_1829_);
lean_ctor_set(v___x_1864_, 1, v___x_1860_);
lean_ctor_set(v___x_1864_, 2, v___x_1863_);
lean_ctor_set_float(v___x_1864_, sizeof(void*)*3, v___x_1861_);
lean_ctor_set_float(v___x_1864_, sizeof(void*)*3 + 8, v___x_1861_);
lean_ctor_set_uint8(v___x_1864_, sizeof(void*)*3 + 16, v___x_1862_);
v___x_1865_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__2));
v___x_1866_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v_a_1838_);
lean_ctor_set(v___x_1866_, 2, v___x_1865_);
lean_inc(v_ref_1836_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_ref_1836_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_PersistentArray_push___redArg(v_traces_1856_, v___x_1867_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1868_);
v___x_1870_ = v___x_1858_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1868_);
lean_ctor_set_uint64(v_reuseFailAlloc_1879_, sizeof(void*)*1, v_tid_1855_);
v___x_1870_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1872_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 4, v___x_1870_);
v___x_1872_ = v___x_1853_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_env_1844_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_nextMacroScope_1845_);
lean_ctor_set(v_reuseFailAlloc_1878_, 2, v_ngen_1846_);
lean_ctor_set(v_reuseFailAlloc_1878_, 3, v_auxDeclNGen_1847_);
lean_ctor_set(v_reuseFailAlloc_1878_, 4, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1878_, 5, v_cache_1848_);
lean_ctor_set(v_reuseFailAlloc_1878_, 6, v_messages_1849_);
lean_ctor_set(v_reuseFailAlloc_1878_, 7, v_infoState_1850_);
lean_ctor_set(v_reuseFailAlloc_1878_, 8, v_snapshotTasks_1851_);
v___x_1872_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1873_ = lean_st_ref_set(v___y_1834_, v___x_1872_);
v___x_1874_ = lean_box(0);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1874_);
v___x_1876_ = v___x_1840_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___boxed(lean_object* v_cls_1883_, lean_object* v_msg_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(v_cls_1883_, v_msg_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1890_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(lean_object* v___x_1891_, lean_object* v_as_1892_, size_t v_i_1893_, size_t v_stop_1894_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_usize_dec_eq(v_i_1893_, v_stop_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v_defValue_1897_; uint8_t v___x_1898_; uint8_t v___y_1904_; uint8_t v___x_1905_; 
v___x_1896_ = lean_array_uget_borrowed(v_as_1892_, v_i_1893_);
v_defValue_1897_ = lean_ctor_get(v___x_1896_, 1);
v___x_1898_ = 1;
v___x_1905_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v___x_1891_, v___x_1896_);
if (v___x_1905_ == 0)
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_unbox(v_defValue_1897_);
if (v___x_1906_ == 0)
{
goto v___jp_1899_;
}
else
{
v___y_1904_ = v___x_1905_;
goto v___jp_1903_;
}
}
else
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_unbox(v_defValue_1897_);
v___y_1904_ = v___x_1907_;
goto v___jp_1903_;
}
v___jp_1899_:
{
if (v___x_1895_ == 0)
{
size_t v___x_1900_; size_t v___x_1901_; 
v___x_1900_ = ((size_t)1ULL);
v___x_1901_ = lean_usize_add(v_i_1893_, v___x_1900_);
v_i_1893_ = v___x_1901_;
goto _start;
}
else
{
return v___x_1898_;
}
}
v___jp_1903_:
{
if (v___y_1904_ == 0)
{
return v___x_1898_;
}
else
{
goto v___jp_1899_;
}
}
}
else
{
uint8_t v___x_1908_; 
v___x_1908_ = 0;
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object* v___x_1909_, lean_object* v_as_1910_, lean_object* v_i_1911_, lean_object* v_stop_1912_){
_start:
{
size_t v_i_boxed_1913_; size_t v_stop_boxed_1914_; uint8_t v_res_1915_; lean_object* v_r_1916_; 
v_i_boxed_1913_ = lean_unbox_usize(v_i_1911_);
lean_dec(v_i_1911_);
v_stop_boxed_1914_ = lean_unbox_usize(v_stop_1912_);
lean_dec(v_stop_1912_);
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v___x_1909_, v_as_1910_, v_i_boxed_1913_, v_stop_boxed_1914_);
lean_dec_ref(v_as_1910_);
lean_dec_ref(v___x_1909_);
v_r_1916_ = lean_box(v_res_1915_);
return v_r_1916_;
}
}
static uint8_t _init_l_Lean_Meta_generateEagerEqns___closed__0(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = lean_obj_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = lean_nat_dec_lt(v___x_1918_, v___x_1917_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__4(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_1927_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_1928_ = l_Lean_Name_append(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__6(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__5));
v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object* v_declName_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = l_Lean_Meta_eqnAffectingOptions;
v___x_1965_ = lean_uint8_once(&l_Lean_Meta_generateEagerEqns___closed__0, &l_Lean_Meta_generateEagerEqns___closed__0_once, _init_l_Lean_Meta_generateEagerEqns___closed__0);
if (v___x_1965_ == 0)
{
lean_dec(v_declName_1932_);
goto v___jp_1938_;
}
else
{
if (v___x_1965_ == 0)
{
lean_dec(v_declName_1932_);
goto v___jp_1938_;
}
else
{
lean_object* v_options_1966_; lean_object* v_inheritedTraceOptions_1967_; size_t v___x_1968_; size_t v___x_1969_; uint8_t v___x_1970_; 
v_options_1966_ = lean_ctor_get(v_a_1935_, 2);
v_inheritedTraceOptions_1967_ = lean_ctor_get(v_a_1935_, 13);
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_once(&l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2, &l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_generateEagerEqns_spec__0(v_options_1966_, v___x_1964_, v___x_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_dec(v_declName_1932_);
goto v___jp_1938_;
}
else
{
uint8_t v_hasTrace_1971_; 
v_hasTrace_1971_ = lean_ctor_get_uint8(v_options_1966_, sizeof(void*)*1);
if (v_hasTrace_1971_ == 0)
{
v___y_1942_ = v_a_1933_;
v___y_1943_ = v_a_1934_;
v___y_1944_ = v_a_1935_;
v___y_1945_ = v_a_1936_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1972_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_1973_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__4, &l_Lean_Meta_generateEagerEqns___closed__4_once, _init_l_Lean_Meta_generateEagerEqns___closed__4);
v___x_1974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1967_, v_options_1966_, v___x_1973_);
if (v___x_1974_ == 0)
{
v___y_1942_ = v_a_1933_;
v___y_1943_ = v_a_1934_;
v___y_1944_ = v_a_1935_;
v___y_1945_ = v_a_1936_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1975_ = lean_obj_once(&l_Lean_Meta_generateEagerEqns___closed__6, &l_Lean_Meta_generateEagerEqns___closed__6_once, _init_l_Lean_Meta_generateEagerEqns___closed__6);
lean_inc(v_declName_1932_);
v___x_1976_ = l_Lean_MessageData_ofName(v_declName_1932_);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1(v___x_1972_, v___x_1977_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_dec_ref(v___x_1978_);
v___y_1942_ = v_a_1933_;
v___y_1943_ = v_a_1934_;
v___y_1944_ = v_a_1935_;
v___y_1945_ = v_a_1936_;
goto v___jp_1941_;
}
else
{
lean_dec(v_declName_1932_);
return v___x_1978_;
}
}
}
}
}
}
v___jp_1938_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
v___jp_1941_:
{
lean_object* v___x_1946_; 
v___x_1946_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1932_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1954_; 
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v___x_1946_, 0);
lean_dec(v_unused_1955_);
v___x_1948_ = v___x_1946_;
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
else
{
lean_dec(v___x_1946_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_box(0);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1950_);
v___x_1952_ = v___x_1948_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
v_a_1956_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1946_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1946_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___boxed(lean_object* v_declName_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Meta_generateEagerEqns(v_declName_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_st_mk_ref(v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2011_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2011_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2011_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_unbox(v_a_1995_);
lean_dec(v_a_1995_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
lean_dec_ref(v_f_1992_);
v___x_2000_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
lean_ctor_set(v___x_1997_, 0, v___x_2000_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2004_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2005_ = lean_st_ref_take(v___x_2004_);
v___x_2006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_f_1992_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = lean_st_ref_set(v___x_2004_, v___x_2006_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2007_);
v___x_2009_ = v___x_1997_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_f_1992_);
v_a_2012_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1994_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1994_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2026_, lean_object* v_as_x27_2027_, lean_object* v_b_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
if (lean_obj_tag(v_as_x27_2027_) == 0)
{
lean_object* v___x_2034_; 
lean_dec(v_declName_2026_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_b_2028_);
return v___x_2034_;
}
else
{
lean_object* v_head_2035_; lean_object* v_tail_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v_b_2028_);
v_head_2035_ = lean_ctor_get(v_as_x27_2027_, 0);
v_tail_2036_ = lean_ctor_get(v_as_x27_2027_, 1);
lean_inc(v_head_2035_);
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2031_);
lean_inc(v___y_2030_);
lean_inc_ref(v___y_2029_);
lean_inc(v_declName_2026_);
v___x_2037_ = lean_apply_6(v_head_2035_, v_declName_2026_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, lean_box(0));
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2050_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2050_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2050_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_box(0);
if (lean_obj_tag(v_a_2038_) == 1)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
lean_dec(v_declName_2026_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_a_2038_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2042_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2044_);
v___x_2046_ = v___x_2040_;
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
else
{
lean_object* v___x_2048_; 
lean_del_object(v___x_2040_);
lean_dec(v_a_2038_);
v___x_2048_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2027_ = v_tail_2036_;
v_b_2028_ = v___x_2048_;
goto _start;
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_declName_2026_);
v_a_2051_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2037_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2037_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2059_, lean_object* v_as_x27_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2059_, v_as_x27_2060_, v_b_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v_as_x27_2060_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2068_, lean_object* v_declName_2069_, uint8_t v_nonRec_2070_, lean_object* v___x_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2080_; lean_object* v_env_2081_; uint8_t v___x_2082_; uint8_t v___x_2083_; 
v___x_2080_ = lean_st_ref_get(v___y_2075_);
v_env_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_ref(v_env_2081_);
lean_dec(v___x_2080_);
v___x_2082_ = 1;
lean_inc(v___x_2068_);
v___x_2083_ = l_Lean_Environment_contains(v_env_2081_, v___x_2068_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
lean_dec(v___x_2068_);
lean_inc(v_declName_2069_);
v___x_2084_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2069_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = lean_unbox(v_a_2085_);
lean_dec(v_a_2085_);
if (v___x_2086_ == 0)
{
lean_dec_ref(v___x_2071_);
lean_dec(v_declName_2069_);
goto v___jp_2077_;
}
else
{
lean_object* v___x_2087_; 
lean_inc(v_declName_2069_);
v___x_2087_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2069_, v___y_2075_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; uint8_t v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = lean_unbox(v_a_2088_);
lean_dec(v_a_2088_);
if (v___x_2089_ == 0)
{
if (v_nonRec_2070_ == 0)
{
lean_dec_ref(v___x_2071_);
lean_dec(v_declName_2069_);
goto v___jp_2077_;
}
else
{
lean_object* v___x_2090_; lean_object* v_env_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2090_ = lean_st_ref_get(v___y_2075_);
v_env_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc_ref(v_env_2091_);
lean_dec(v___x_2090_);
lean_inc(v_declName_2069_);
v___x_2092_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2091_, v_declName_2069_, v___x_2071_);
v___x_2093_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2069_, v___x_2092_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2093_;
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec_ref(v___x_2071_);
v___x_2094_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2095_ = lean_st_ref_get(v___x_2094_);
v___x_2096_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2097_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2069_, v___x_2095_, v___x_2096_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___x_2095_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2107_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_fst_2102_; 
v_fst_2102_ = lean_ctor_get(v_a_2098_, 0);
lean_inc(v_fst_2102_);
lean_dec(v_a_2098_);
if (lean_obj_tag(v_fst_2102_) == 0)
{
lean_del_object(v___x_2100_);
goto v___jp_2077_;
}
else
{
lean_object* v_val_2103_; lean_object* v___x_2105_; 
v_val_2103_ = lean_ctor_get(v_fst_2102_, 0);
lean_inc(v_val_2103_);
lean_dec_ref(v_fst_2102_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v_val_2103_);
v___x_2105_ = v___x_2100_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_val_2103_);
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
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v_a_2108_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2097_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2097_);
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
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v___x_2071_);
lean_dec(v_declName_2069_);
v_a_2116_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2087_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2087_);
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
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v___x_2071_);
lean_dec(v_declName_2069_);
v_a_2124_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2084_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2084_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
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
lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref(v___x_2071_);
lean_dec(v_declName_2069_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2068_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
v___jp_2077_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2134_, lean_object* v_declName_2135_, lean_object* v_nonRec_2136_, lean_object* v___x_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v_nonRec_boxed_2143_; lean_object* v_res_2144_; 
v_nonRec_boxed_2143_ = lean_unbox(v_nonRec_2136_);
v_res_2144_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2134_, v_declName_2135_, v_nonRec_boxed_2143_, v___x_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_ref_2151_; lean_object* v___x_2152_; lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2161_; 
v_ref_2151_ = lean_ctor_get(v___y_2148_, 5);
v___x_2152_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1_spec__1(v_msg_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_inc(v_ref_2151_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v_ref_2151_);
lean_ctor_set(v___x_2157_, 1, v_a_2153_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 1);
lean_ctor_set(v___x_2155_, 0, v___x_2157_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2169_, uint8_t v_isExporting_2170_, lean_object* v___x_2171_, lean_object* v___y_2172_, lean_object* v___x_2173_, lean_object* v_a_x3f_2174_){
_start:
{
lean_object* v___x_2176_; lean_object* v_env_2177_; lean_object* v_nextMacroScope_2178_; lean_object* v_ngen_2179_; lean_object* v_auxDeclNGen_2180_; lean_object* v_traceState_2181_; lean_object* v_messages_2182_; lean_object* v_infoState_2183_; lean_object* v_snapshotTasks_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2209_; 
v___x_2176_ = lean_st_ref_take(v___y_2169_);
v_env_2177_ = lean_ctor_get(v___x_2176_, 0);
v_nextMacroScope_2178_ = lean_ctor_get(v___x_2176_, 1);
v_ngen_2179_ = lean_ctor_get(v___x_2176_, 2);
v_auxDeclNGen_2180_ = lean_ctor_get(v___x_2176_, 3);
v_traceState_2181_ = lean_ctor_get(v___x_2176_, 4);
v_messages_2182_ = lean_ctor_get(v___x_2176_, 6);
v_infoState_2183_ = lean_ctor_get(v___x_2176_, 7);
v_snapshotTasks_2184_ = lean_ctor_get(v___x_2176_, 8);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v___x_2176_, 5);
lean_dec(v_unused_2210_);
v___x_2186_ = v___x_2176_;
v_isShared_2187_ = v_isSharedCheck_2209_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snapshotTasks_2184_);
lean_inc(v_infoState_2183_);
lean_inc(v_messages_2182_);
lean_inc(v_traceState_2181_);
lean_inc(v_auxDeclNGen_2180_);
lean_inc(v_ngen_2179_);
lean_inc(v_nextMacroScope_2178_);
lean_inc(v_env_2177_);
lean_dec(v___x_2176_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2209_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2188_ = l_Lean_Environment_setExporting(v_env_2177_, v_isExporting_2170_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 5, v___x_2171_);
lean_ctor_set(v___x_2186_, 0, v___x_2188_);
v___x_2190_ = v___x_2186_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_nextMacroScope_2178_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_ngen_2179_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_auxDeclNGen_2180_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_traceState_2181_);
lean_ctor_set(v_reuseFailAlloc_2208_, 5, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2208_, 6, v_messages_2182_);
lean_ctor_set(v_reuseFailAlloc_2208_, 7, v_infoState_2183_);
lean_ctor_set(v_reuseFailAlloc_2208_, 8, v_snapshotTasks_2184_);
v___x_2190_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_mctx_2193_; lean_object* v_zetaDeltaFVarIds_2194_; lean_object* v_postponed_2195_; lean_object* v_diag_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2206_; 
v___x_2191_ = lean_st_ref_set(v___y_2169_, v___x_2190_);
v___x_2192_ = lean_st_ref_take(v___y_2172_);
v_mctx_2193_ = lean_ctor_get(v___x_2192_, 0);
v_zetaDeltaFVarIds_2194_ = lean_ctor_get(v___x_2192_, 2);
v_postponed_2195_ = lean_ctor_get(v___x_2192_, 3);
v_diag_2196_ = lean_ctor_get(v___x_2192_, 4);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v___x_2192_, 1);
lean_dec(v_unused_2207_);
v___x_2198_ = v___x_2192_;
v_isShared_2199_ = v_isSharedCheck_2206_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_diag_2196_);
lean_inc(v_postponed_2195_);
lean_inc(v_zetaDeltaFVarIds_2194_);
lean_inc(v_mctx_2193_);
lean_dec(v___x_2192_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2206_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v___x_2173_);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_mctx_2193_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_zetaDeltaFVarIds_2194_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_postponed_2195_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_diag_2196_);
v___x_2201_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_st_ref_set(v___y_2172_, v___x_2201_);
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2211_, lean_object* v_isExporting_2212_, lean_object* v___x_2213_, lean_object* v___y_2214_, lean_object* v___x_2215_, lean_object* v_a_x3f_2216_, lean_object* v___y_2217_){
_start:
{
uint8_t v_isExporting_boxed_2218_; lean_object* v_res_2219_; 
v_isExporting_boxed_2218_ = lean_unbox(v_isExporting_2212_);
v_res_2219_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2211_, v_isExporting_boxed_2218_, v___x_2213_, v___y_2214_, v___x_2215_, v_a_x3f_2216_);
lean_dec(v_a_x3f_2216_);
lean_dec(v___y_2214_);
lean_dec(v___y_2211_);
return v_res_2219_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__1);
v___x_2221_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
lean_ctor_set(v___x_2221_, 2, v___x_2220_);
lean_ctor_set(v___x_2221_, 3, v___x_2220_);
lean_ctor_set(v___x_2221_, 4, v___x_2220_);
lean_ctor_set(v___x_2221_, 5, v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2222_, uint8_t v_isExporting_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; lean_object* v_env_2230_; uint8_t v_isExporting_2231_; lean_object* v___x_2232_; lean_object* v_env_2233_; lean_object* v_nextMacroScope_2234_; lean_object* v_ngen_2235_; lean_object* v_auxDeclNGen_2236_; lean_object* v_traceState_2237_; lean_object* v_messages_2238_; lean_object* v_infoState_2239_; lean_object* v_snapshotTasks_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2294_; 
v___x_2229_ = lean_st_ref_get(v___y_2227_);
v_env_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc_ref(v_env_2230_);
lean_dec(v___x_2229_);
v_isExporting_2231_ = lean_ctor_get_uint8(v_env_2230_, sizeof(void*)*8);
lean_dec_ref(v_env_2230_);
v___x_2232_ = lean_st_ref_take(v___y_2227_);
v_env_2233_ = lean_ctor_get(v___x_2232_, 0);
v_nextMacroScope_2234_ = lean_ctor_get(v___x_2232_, 1);
v_ngen_2235_ = lean_ctor_get(v___x_2232_, 2);
v_auxDeclNGen_2236_ = lean_ctor_get(v___x_2232_, 3);
v_traceState_2237_ = lean_ctor_get(v___x_2232_, 4);
v_messages_2238_ = lean_ctor_get(v___x_2232_, 6);
v_infoState_2239_ = lean_ctor_get(v___x_2232_, 7);
v_snapshotTasks_2240_ = lean_ctor_get(v___x_2232_, 8);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; 
v_unused_2295_ = lean_ctor_get(v___x_2232_, 5);
lean_dec(v_unused_2295_);
v___x_2242_ = v___x_2232_;
v_isShared_2243_ = v_isSharedCheck_2294_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_snapshotTasks_2240_);
lean_inc(v_infoState_2239_);
lean_inc(v_messages_2238_);
lean_inc(v_traceState_2237_);
lean_inc(v_auxDeclNGen_2236_);
lean_inc(v_ngen_2235_);
lean_inc(v_nextMacroScope_2234_);
lean_inc(v_env_2233_);
lean_dec(v___x_2232_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2294_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2244_ = l_Lean_Environment_setExporting(v_env_2233_, v_isExporting_2223_);
v___x_2245_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___closed__2);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 5, v___x_2245_);
lean_ctor_set(v___x_2242_, 0, v___x_2244_);
v___x_2247_ = v___x_2242_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_nextMacroScope_2234_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_ngen_2235_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_auxDeclNGen_2236_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_traceState_2237_);
lean_ctor_set(v_reuseFailAlloc_2293_, 5, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2293_, 6, v_messages_2238_);
lean_ctor_set(v_reuseFailAlloc_2293_, 7, v_infoState_2239_);
lean_ctor_set(v_reuseFailAlloc_2293_, 8, v_snapshotTasks_2240_);
v___x_2247_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_mctx_2250_; lean_object* v_zetaDeltaFVarIds_2251_; lean_object* v_postponed_2252_; lean_object* v_diag_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2291_; 
v___x_2248_ = lean_st_ref_set(v___y_2227_, v___x_2247_);
v___x_2249_ = lean_st_ref_take(v___y_2225_);
v_mctx_2250_ = lean_ctor_get(v___x_2249_, 0);
v_zetaDeltaFVarIds_2251_ = lean_ctor_get(v___x_2249_, 2);
v_postponed_2252_ = lean_ctor_get(v___x_2249_, 3);
v_diag_2253_ = lean_ctor_get(v___x_2249_, 4);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v___x_2249_, 1);
lean_dec(v_unused_2292_);
v___x_2255_ = v___x_2249_;
v_isShared_2256_ = v_isSharedCheck_2291_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_diag_2253_);
lean_inc(v_postponed_2252_);
lean_inc(v_zetaDeltaFVarIds_2251_);
lean_inc(v_mctx_2250_);
lean_dec(v___x_2249_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2291_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___closed__0);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 1, v___x_2257_);
v___x_2259_ = v___x_2255_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_mctx_2250_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_zetaDeltaFVarIds_2251_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_postponed_2252_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v_diag_2253_);
v___x_2259_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v_r_2261_; 
v___x_2260_ = lean_st_ref_set(v___y_2225_, v___x_2259_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v___y_2225_);
lean_inc_ref(v___y_2224_);
v_r_2261_ = lean_apply_5(v_x_2222_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, lean_box(0));
if (lean_obj_tag(v_r_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2278_; 
v_a_2262_ = lean_ctor_get(v_r_2261_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_r_2261_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2264_ = v_r_2261_;
v_isShared_2265_ = v_isSharedCheck_2278_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v_r_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2278_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
lean_inc(v_a_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 1);
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v___x_2268_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2227_, v_isExporting_2231_, v___x_2245_, v___y_2225_, v___x_2257_, v___x_2267_);
lean_dec_ref(v___x_2267_);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2275_ == 0)
{
lean_object* v_unused_2276_; 
v_unused_2276_ = lean_ctor_get(v___x_2268_, 0);
lean_dec(v_unused_2276_);
v___x_2270_ = v___x_2268_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_dec(v___x_2268_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v_a_2262_);
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2262_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2279_ = lean_ctor_get(v_r_2261_, 0);
lean_inc(v_a_2279_);
lean_dec_ref(v_r_2261_);
v___x_2280_ = lean_box(0);
v___x_2281_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2227_, v_isExporting_2231_, v___x_2245_, v___y_2225_, v___x_2257_, v___x_2280_);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; 
v_unused_2289_ = lean_ctor_get(v___x_2281_, 0);
lean_dec(v_unused_2289_);
v___x_2283_ = v___x_2281_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v___x_2281_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 1);
lean_ctor_set(v___x_2283_, 0, v_a_2279_);
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2279_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2296_, lean_object* v_isExporting_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
uint8_t v_isExporting_boxed_2303_; lean_object* v_res_2304_; 
v_isExporting_boxed_2303_ = lean_unbox(v_isExporting_2297_);
v_res_2304_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2296_, v_isExporting_boxed_2303_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2305_, uint8_t v_when_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
if (v_when_2306_ == 0)
{
lean_object* v___x_2312_; 
lean_inc(v___y_2310_);
lean_inc_ref(v___y_2309_);
lean_inc(v___y_2308_);
lean_inc_ref(v___y_2307_);
v___x_2312_ = lean_apply_5(v_x_2305_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, lean_box(0));
return v___x_2312_;
}
else
{
uint8_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = 0;
v___x_2314_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2305_, v___x_2313_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2315_, lean_object* v_when_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
uint8_t v_when_boxed_2322_; lean_object* v_res_2323_; 
v_when_boxed_2322_ = lean_unbox(v_when_2316_);
v_res_2323_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2315_, v_when_boxed_2322_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2323_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2326_ = l_Lean_stringToMessageData(v___x_2325_);
return v___x_2326_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2329_ = l_Lean_stringToMessageData(v___x_2328_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2332_ = l_Lean_stringToMessageData(v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2333_, uint8_t v_nonRec_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; lean_object* v_env_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___f_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2340_ = lean_st_ref_get(v___y_2338_);
v_env_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc_ref(v_env_2341_);
lean_dec(v___x_2340_);
v___x_2342_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2333_);
v___x_2343_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2341_, v_declName_2333_, v___x_2342_);
v___x_2344_ = lean_box(v_nonRec_2334_);
lean_inc(v___x_2343_);
v___f_2345_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2345_, 0, v___x_2343_);
lean_closure_set(v___f_2345_, 1, v_declName_2333_);
lean_closure_set(v___f_2345_, 2, v___x_2344_);
lean_closure_set(v___f_2345_, 3, v___x_2342_);
v___x_2346_ = 1;
v___x_2347_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2345_, v___x_2346_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
if (lean_obj_tag(v_a_2348_) == 1)
{
lean_object* v_val_2349_; uint8_t v___x_2350_; 
v_val_2349_ = lean_ctor_get(v_a_2348_, 0);
lean_inc(v_val_2349_);
lean_dec_ref(v_a_2348_);
v___x_2350_ = lean_name_eq(v_val_2349_, v___x_2343_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v___x_2347_);
v___x_2351_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2352_ = l_Lean_MessageData_ofName(v_val_2349_);
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = l_Lean_MessageData_ofName(v___x_2343_);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2359_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_dec(v_val_2349_);
lean_dec(v___x_2343_);
return v___x_2347_;
}
}
else
{
lean_dec(v_a_2348_);
lean_dec(v___x_2343_);
return v___x_2347_;
}
}
else
{
lean_dec(v___x_2343_);
return v___x_2347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2369_, lean_object* v_nonRec_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
uint8_t v_nonRec_boxed_2376_; lean_object* v_res_2377_; 
v_nonRec_boxed_2376_ = lean_unbox(v_nonRec_2370_);
v_res_2377_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2369_, v_nonRec_boxed_2376_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2378_, uint8_t v_nonRec_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2385_ = lean_box(v_nonRec_2379_);
v___f_2386_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2386_, 0, v_declName_2378_);
lean_closure_set(v___f_2386_, 1, v___x_2385_);
v___x_2387_ = lean_unsigned_to_nat(32u);
v___x_2388_ = lean_mk_empty_array_with_capacity(v___x_2387_);
lean_dec_ref(v___x_2388_);
v___x_2389_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2391_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2389_, v___x_2390_, v___f_2386_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2392_, lean_object* v_nonRec_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
uint8_t v_nonRec_boxed_2399_; lean_object* v_res_2400_; 
v_nonRec_boxed_2399_ = lean_unbox(v_nonRec_2393_);
v_res_2400_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2392_, v_nonRec_boxed_2399_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2401_, lean_object* v_as_2402_, lean_object* v_as_x27_2403_, lean_object* v_b_2404_, lean_object* v_a_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2401_, v_as_x27_2403_, v_b_2404_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2412_, lean_object* v_as_2413_, lean_object* v_as_x27_2414_, lean_object* v_b_2415_, lean_object* v_a_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2412_, v_as_2413_, v_as_x27_2414_, v_b_2415_, v_a_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v_as_x27_2414_);
lean_dec(v_as_2413_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2423_, lean_object* v_x_2424_, uint8_t v_isExporting_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2424_, v_isExporting_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_x_2433_, lean_object* v_isExporting_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
uint8_t v_isExporting_boxed_2440_; lean_object* v_res_2441_; 
v_isExporting_boxed_2440_ = lean_unbox(v_isExporting_2434_);
v_res_2441_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2432_, v_x_2433_, v_isExporting_boxed_2440_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2442_, lean_object* v_x_2443_, uint8_t v_when_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2443_, v_when_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2451_, lean_object* v_x_2452_, lean_object* v_when_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v_when_boxed_2459_; lean_object* v_res_2460_; 
v_when_boxed_2459_ = lean_unbox(v_when_2453_);
v_res_2460_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2451_, v_x_2452_, v_when_boxed_2459_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2461_, lean_object* v_msg_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_msg_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2469_, v_msg_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2476_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_unsigned_to_nat(32u);
v___x_2478_ = lean_mk_empty_array_with_capacity(v___x_2477_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2480_ = ((size_t)5ULL);
v___x_2481_ = lean_unsigned_to_nat(0u);
v___x_2482_ = lean_unsigned_to_nat(32u);
v___x_2483_ = lean_mk_empty_array_with_capacity(v___x_2482_);
v___x_2484_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2485_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v___x_2483_);
lean_ctor_set(v___x_2485_, 2, v___x_2481_);
lean_ctor_set(v___x_2485_, 3, v___x_2481_);
lean_ctor_set_usize(v___x_2485_, 4, v___x_2480_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; lean_object* v_traceState_2489_; lean_object* v_traces_2490_; lean_object* v___x_2491_; lean_object* v_traceState_2492_; lean_object* v_env_2493_; lean_object* v_nextMacroScope_2494_; lean_object* v_ngen_2495_; lean_object* v_auxDeclNGen_2496_; lean_object* v_cache_2497_; lean_object* v_messages_2498_; lean_object* v_infoState_2499_; lean_object* v_snapshotTasks_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2519_; 
v___x_2488_ = lean_st_ref_get(v___y_2486_);
v_traceState_2489_ = lean_ctor_get(v___x_2488_, 4);
lean_inc_ref(v_traceState_2489_);
lean_dec(v___x_2488_);
v_traces_2490_ = lean_ctor_get(v_traceState_2489_, 0);
lean_inc_ref(v_traces_2490_);
lean_dec_ref(v_traceState_2489_);
v___x_2491_ = lean_st_ref_take(v___y_2486_);
v_traceState_2492_ = lean_ctor_get(v___x_2491_, 4);
v_env_2493_ = lean_ctor_get(v___x_2491_, 0);
v_nextMacroScope_2494_ = lean_ctor_get(v___x_2491_, 1);
v_ngen_2495_ = lean_ctor_get(v___x_2491_, 2);
v_auxDeclNGen_2496_ = lean_ctor_get(v___x_2491_, 3);
v_cache_2497_ = lean_ctor_get(v___x_2491_, 5);
v_messages_2498_ = lean_ctor_get(v___x_2491_, 6);
v_infoState_2499_ = lean_ctor_get(v___x_2491_, 7);
v_snapshotTasks_2500_ = lean_ctor_get(v___x_2491_, 8);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2502_ = v___x_2491_;
v_isShared_2503_ = v_isSharedCheck_2519_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_snapshotTasks_2500_);
lean_inc(v_infoState_2499_);
lean_inc(v_messages_2498_);
lean_inc(v_cache_2497_);
lean_inc(v_traceState_2492_);
lean_inc(v_auxDeclNGen_2496_);
lean_inc(v_ngen_2495_);
lean_inc(v_nextMacroScope_2494_);
lean_inc(v_env_2493_);
lean_dec(v___x_2491_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2519_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
uint64_t v_tid_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2517_; 
v_tid_2504_ = lean_ctor_get_uint64(v_traceState_2492_, sizeof(void*)*1);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_traceState_2492_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v_traceState_2492_, 0);
lean_dec(v_unused_2518_);
v___x_2506_ = v_traceState_2492_;
v_isShared_2507_ = v_isSharedCheck_2517_;
goto v_resetjp_2505_;
}
else
{
lean_dec(v_traceState_2492_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2517_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2508_);
lean_ctor_set_uint64(v_reuseFailAlloc_2516_, sizeof(void*)*1, v_tid_2504_);
v___x_2510_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 4, v___x_2510_);
v___x_2512_ = v___x_2502_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_env_2493_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_nextMacroScope_2494_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_ngen_2495_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_auxDeclNGen_2496_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2515_, 5, v_cache_2497_);
lean_ctor_set(v_reuseFailAlloc_2515_, 6, v_messages_2498_);
lean_ctor_set(v_reuseFailAlloc_2515_, 7, v_infoState_2499_);
lean_ctor_set(v_reuseFailAlloc_2515_, 8, v_snapshotTasks_2500_);
v___x_2512_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_st_ref_set(v___y_2486_, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_traces_2490_);
return v___x_2514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2520_);
lean_dec(v___y_2520_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = 0;
v___x_2536_ = lean_box(v___x_2535_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
return v_res_2542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2552_ = l_Lean_MessageData_ofName(v_name_2546_);
v___x_2553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2555_, v_x_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v_x_2556_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_x_2561_){
_start:
{
if (lean_obj_tag(v_x_2561_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v_x_2561_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_x_2561_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v_x_2561_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v_x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set_tag(v___x_2565_, 1);
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
v_a_2571_ = lean_ctor_get(v_x_2561_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_x_2561_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v_x_2561_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v_x_2561_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 0);
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object* v_x_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_2579_);
return v_res_2581_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_e_2582_){
_start:
{
if (lean_obj_tag(v_e_2582_) == 0)
{
uint8_t v___x_2583_; 
v___x_2583_ = 2;
return v___x_2583_;
}
else
{
lean_object* v_a_2584_; uint8_t v___x_2585_; 
v_a_2584_ = lean_ctor_get(v_e_2582_, 0);
v___x_2585_ = lean_unbox(v_a_2584_);
if (v___x_2585_ == 0)
{
uint8_t v___x_2586_; 
v___x_2586_ = 1;
return v___x_2586_;
}
else
{
uint8_t v___x_2587_; 
v___x_2587_ = 0;
return v___x_2587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_e_2588_){
_start:
{
uint8_t v_res_2589_; lean_object* v_r_2590_; 
v_res_2589_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_e_2588_);
lean_dec_ref(v_e_2588_);
v_r_2590_ = lean_box(v_res_2589_);
return v_r_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(size_t v_sz_2591_, size_t v_i_2592_, lean_object* v_bs_2593_){
_start:
{
uint8_t v___x_2594_; 
v___x_2594_ = lean_usize_dec_lt(v_i_2592_, v_sz_2591_);
if (v___x_2594_ == 0)
{
return v_bs_2593_;
}
else
{
lean_object* v_v_2595_; lean_object* v_msg_2596_; lean_object* v___x_2597_; lean_object* v_bs_x27_2598_; size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; 
v_v_2595_ = lean_array_uget_borrowed(v_bs_2593_, v_i_2592_);
v_msg_2596_ = lean_ctor_get(v_v_2595_, 1);
lean_inc_ref(v_msg_2596_);
v___x_2597_ = lean_unsigned_to_nat(0u);
v_bs_x27_2598_ = lean_array_uset(v_bs_2593_, v_i_2592_, v___x_2597_);
v___x_2599_ = ((size_t)1ULL);
v___x_2600_ = lean_usize_add(v_i_2592_, v___x_2599_);
v___x_2601_ = lean_array_uset(v_bs_x27_2598_, v_i_2592_, v_msg_2596_);
v_i_2592_ = v___x_2600_;
v_bs_2593_ = v___x_2601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_sz_2603_, lean_object* v_i_2604_, lean_object* v_bs_2605_){
_start:
{
size_t v_sz_boxed_2606_; size_t v_i_boxed_2607_; lean_object* v_res_2608_; 
v_sz_boxed_2606_ = lean_unbox_usize(v_sz_2603_);
lean_dec(v_sz_2603_);
v_i_boxed_2607_ = lean_unbox_usize(v_i_2604_);
lean_dec(v_i_2604_);
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_boxed_2606_, v_i_boxed_2607_, v_bs_2605_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_oldTraces_2609_, lean_object* v_data_2610_, lean_object* v_ref_2611_, lean_object* v_msg_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_fileName_2616_; lean_object* v_fileMap_2617_; lean_object* v_options_2618_; lean_object* v_currRecDepth_2619_; lean_object* v_maxRecDepth_2620_; lean_object* v_ref_2621_; lean_object* v_currNamespace_2622_; lean_object* v_openDecls_2623_; lean_object* v_initHeartbeats_2624_; lean_object* v_maxHeartbeats_2625_; lean_object* v_quotContext_2626_; lean_object* v_currMacroScope_2627_; uint8_t v_diag_2628_; lean_object* v_cancelTk_x3f_2629_; uint8_t v_suppressElabErrors_2630_; lean_object* v_inheritedTraceOptions_2631_; lean_object* v___x_2632_; lean_object* v_traceState_2633_; lean_object* v_traces_2634_; lean_object* v_ref_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; size_t v_sz_2638_; size_t v___x_2639_; lean_object* v___x_2640_; lean_object* v_msg_2641_; lean_object* v___x_2642_; lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2680_; 
v_fileName_2616_ = lean_ctor_get(v___y_2613_, 0);
v_fileMap_2617_ = lean_ctor_get(v___y_2613_, 1);
v_options_2618_ = lean_ctor_get(v___y_2613_, 2);
v_currRecDepth_2619_ = lean_ctor_get(v___y_2613_, 3);
v_maxRecDepth_2620_ = lean_ctor_get(v___y_2613_, 4);
v_ref_2621_ = lean_ctor_get(v___y_2613_, 5);
v_currNamespace_2622_ = lean_ctor_get(v___y_2613_, 6);
v_openDecls_2623_ = lean_ctor_get(v___y_2613_, 7);
v_initHeartbeats_2624_ = lean_ctor_get(v___y_2613_, 8);
v_maxHeartbeats_2625_ = lean_ctor_get(v___y_2613_, 9);
v_quotContext_2626_ = lean_ctor_get(v___y_2613_, 10);
v_currMacroScope_2627_ = lean_ctor_get(v___y_2613_, 11);
v_diag_2628_ = lean_ctor_get_uint8(v___y_2613_, sizeof(void*)*14);
v_cancelTk_x3f_2629_ = lean_ctor_get(v___y_2613_, 12);
v_suppressElabErrors_2630_ = lean_ctor_get_uint8(v___y_2613_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2631_ = lean_ctor_get(v___y_2613_, 13);
v___x_2632_ = lean_st_ref_get(v___y_2614_);
v_traceState_2633_ = lean_ctor_get(v___x_2632_, 4);
lean_inc_ref(v_traceState_2633_);
lean_dec(v___x_2632_);
v_traces_2634_ = lean_ctor_get(v_traceState_2633_, 0);
lean_inc_ref(v_traces_2634_);
lean_dec_ref(v_traceState_2633_);
v_ref_2635_ = l_Lean_replaceRef(v_ref_2611_, v_ref_2621_);
lean_inc_ref(v_inheritedTraceOptions_2631_);
lean_inc(v_cancelTk_x3f_2629_);
lean_inc(v_currMacroScope_2627_);
lean_inc(v_quotContext_2626_);
lean_inc(v_maxHeartbeats_2625_);
lean_inc(v_initHeartbeats_2624_);
lean_inc(v_openDecls_2623_);
lean_inc(v_currNamespace_2622_);
lean_inc(v_maxRecDepth_2620_);
lean_inc(v_currRecDepth_2619_);
lean_inc_ref(v_options_2618_);
lean_inc_ref(v_fileMap_2617_);
lean_inc_ref(v_fileName_2616_);
v___x_2636_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2636_, 0, v_fileName_2616_);
lean_ctor_set(v___x_2636_, 1, v_fileMap_2617_);
lean_ctor_set(v___x_2636_, 2, v_options_2618_);
lean_ctor_set(v___x_2636_, 3, v_currRecDepth_2619_);
lean_ctor_set(v___x_2636_, 4, v_maxRecDepth_2620_);
lean_ctor_set(v___x_2636_, 5, v_ref_2635_);
lean_ctor_set(v___x_2636_, 6, v_currNamespace_2622_);
lean_ctor_set(v___x_2636_, 7, v_openDecls_2623_);
lean_ctor_set(v___x_2636_, 8, v_initHeartbeats_2624_);
lean_ctor_set(v___x_2636_, 9, v_maxHeartbeats_2625_);
lean_ctor_set(v___x_2636_, 10, v_quotContext_2626_);
lean_ctor_set(v___x_2636_, 11, v_currMacroScope_2627_);
lean_ctor_set(v___x_2636_, 12, v_cancelTk_x3f_2629_);
lean_ctor_set(v___x_2636_, 13, v_inheritedTraceOptions_2631_);
lean_ctor_set_uint8(v___x_2636_, sizeof(void*)*14, v_diag_2628_);
lean_ctor_set_uint8(v___x_2636_, sizeof(void*)*14 + 1, v_suppressElabErrors_2630_);
v___x_2637_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2634_);
lean_dec_ref(v_traces_2634_);
v_sz_2638_ = lean_array_size(v___x_2637_);
v___x_2639_ = ((size_t)0ULL);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_2638_, v___x_2639_, v___x_2637_);
v_msg_2641_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2641_, 0, v_data_2610_);
lean_ctor_set(v_msg_2641_, 1, v_msg_2612_);
lean_ctor_set(v_msg_2641_, 2, v___x_2640_);
v___x_2642_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2641_, v___x_2636_, v___y_2614_);
lean_dec_ref(v___x_2636_);
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2680_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2680_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v_traceState_2648_; lean_object* v_env_2649_; lean_object* v_nextMacroScope_2650_; lean_object* v_ngen_2651_; lean_object* v_auxDeclNGen_2652_; lean_object* v_cache_2653_; lean_object* v_messages_2654_; lean_object* v_infoState_2655_; lean_object* v_snapshotTasks_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2679_; 
v___x_2647_ = lean_st_ref_take(v___y_2614_);
v_traceState_2648_ = lean_ctor_get(v___x_2647_, 4);
v_env_2649_ = lean_ctor_get(v___x_2647_, 0);
v_nextMacroScope_2650_ = lean_ctor_get(v___x_2647_, 1);
v_ngen_2651_ = lean_ctor_get(v___x_2647_, 2);
v_auxDeclNGen_2652_ = lean_ctor_get(v___x_2647_, 3);
v_cache_2653_ = lean_ctor_get(v___x_2647_, 5);
v_messages_2654_ = lean_ctor_get(v___x_2647_, 6);
v_infoState_2655_ = lean_ctor_get(v___x_2647_, 7);
v_snapshotTasks_2656_ = lean_ctor_get(v___x_2647_, 8);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2658_ = v___x_2647_;
v_isShared_2659_ = v_isSharedCheck_2679_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snapshotTasks_2656_);
lean_inc(v_infoState_2655_);
lean_inc(v_messages_2654_);
lean_inc(v_cache_2653_);
lean_inc(v_traceState_2648_);
lean_inc(v_auxDeclNGen_2652_);
lean_inc(v_ngen_2651_);
lean_inc(v_nextMacroScope_2650_);
lean_inc(v_env_2649_);
lean_dec(v___x_2647_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2679_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
uint64_t v_tid_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2677_; 
v_tid_2660_ = lean_ctor_get_uint64(v_traceState_2648_, sizeof(void*)*1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_traceState_2648_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v_traceState_2648_, 0);
lean_dec(v_unused_2678_);
v___x_2662_ = v_traceState_2648_;
v_isShared_2663_ = v_isSharedCheck_2677_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v_traceState_2648_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2677_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_ref_2611_);
lean_ctor_set(v___x_2664_, 1, v_a_2643_);
v___x_2665_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2609_, v___x_2664_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2665_);
v___x_2667_ = v___x_2662_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2665_);
lean_ctor_set_uint64(v_reuseFailAlloc_2676_, sizeof(void*)*1, v_tid_2660_);
v___x_2667_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2669_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 4, v___x_2667_);
v___x_2669_ = v___x_2658_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_env_2649_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_nextMacroScope_2650_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v_ngen_2651_);
lean_ctor_set(v_reuseFailAlloc_2675_, 3, v_auxDeclNGen_2652_);
lean_ctor_set(v_reuseFailAlloc_2675_, 4, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2675_, 5, v_cache_2653_);
lean_ctor_set(v_reuseFailAlloc_2675_, 6, v_messages_2654_);
lean_ctor_set(v_reuseFailAlloc_2675_, 7, v_infoState_2655_);
lean_ctor_set(v_reuseFailAlloc_2675_, 8, v_snapshotTasks_2656_);
v___x_2669_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2670_ = lean_st_ref_set(v___y_2614_, v___x_2669_);
v___x_2671_ = lean_box(0);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2671_);
v___x_2673_ = v___x_2645_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_oldTraces_2681_, lean_object* v_data_2682_, lean_object* v_ref_2683_, lean_object* v_msg_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2681_, v_data_2682_, v_ref_2683_, v_msg_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2688_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2691_ = l_Lean_stringToMessageData(v___x_2690_);
return v___x_2691_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2));
v___x_2694_ = l_Lean_stringToMessageData(v___x_2693_);
return v___x_2694_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4(void){
_start:
{
lean_object* v___x_2695_; double v___x_2696_; 
v___x_2695_ = lean_unsigned_to_nat(1000u);
v___x_2696_ = lean_float_of_nat(v___x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2697_, uint8_t v_collapsed_2698_, lean_object* v_tag_2699_, lean_object* v_opts_2700_, uint8_t v_clsEnabled_2701_, lean_object* v_oldTraces_2702_, lean_object* v_msg_2703_, lean_object* v_resStartStop_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_fst_2708_; lean_object* v_snd_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2807_; 
v_fst_2708_ = lean_ctor_get(v_resStartStop_2704_, 0);
v_snd_2709_ = lean_ctor_get(v_resStartStop_2704_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_resStartStop_2704_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2711_ = v_resStartStop_2704_;
v_isShared_2712_ = v_isSharedCheck_2807_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snd_2709_);
lean_inc(v_fst_2708_);
lean_dec(v_resStartStop_2704_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2807_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v_data_2716_; lean_object* v_fst_2727_; lean_object* v_snd_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2806_; 
v_fst_2727_ = lean_ctor_get(v_snd_2709_, 0);
v_snd_2728_ = lean_ctor_get(v_snd_2709_, 1);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_snd_2709_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2730_ = v_snd_2709_;
v_isShared_2731_ = v_isSharedCheck_2806_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_snd_2728_);
lean_inc(v_fst_2727_);
lean_dec(v_snd_2709_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2806_;
goto v_resetjp_2729_;
}
v___jp_2713_:
{
lean_object* v___x_2717_; 
lean_inc(v___y_2715_);
v___x_2717_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2702_, v_data_2716_, v___y_2715_, v___y_2714_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v___x_2718_; 
lean_dec_ref(v___x_2717_);
v___x_2718_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2708_);
return v___x_2718_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_fst_2708_);
v_a_2719_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2717_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2717_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; uint8_t v___x_2733_; lean_object* v___y_2735_; lean_object* v_a_2736_; uint8_t v___y_2760_; double v___y_2791_; 
v___x_2732_ = l_Lean_trace_profiler;
v___x_2733_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2700_, v___x_2732_);
if (v___x_2733_ == 0)
{
v___y_2760_ = v___x_2733_;
goto v___jp_2759_;
}
else
{
lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2796_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2797_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_opts_2700_, v___x_2796_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; double v___x_2800_; double v___x_2801_; double v___x_2802_; 
v___x_2798_ = l_Lean_trace_profiler_threshold;
v___x_2799_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2700_, v___x_2798_);
v___x_2800_ = lean_float_of_nat(v___x_2799_);
v___x_2801_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4);
v___x_2802_ = lean_float_div(v___x_2800_, v___x_2801_);
v___y_2791_ = v___x_2802_;
goto v___jp_2790_;
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; double v___x_2805_; 
v___x_2803_ = l_Lean_trace_profiler_threshold;
v___x_2804_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__2(v_opts_2700_, v___x_2803_);
v___x_2805_ = lean_float_of_nat(v___x_2804_);
v___y_2791_ = v___x_2805_;
goto v___jp_2790_;
}
}
v___jp_2734_:
{
uint8_t v_result_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v_result_2737_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_fst_2708_);
v___x_2738_ = l_Lean_TraceResult_toEmoji(v_result_2737_);
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
v___x_2740_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 7);
lean_ctor_set(v___x_2730_, 1, v___x_2740_);
lean_ctor_set(v___x_2730_, 0, v___x_2739_);
v___x_2742_ = v___x_2730_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v_m_2744_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 7);
lean_ctor_set(v___x_2711_, 1, v_a_2736_);
lean_ctor_set(v___x_2711_, 0, v___x_2742_);
v_m_2744_ = v___x_2711_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_a_2736_);
v_m_2744_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; double v___x_2747_; lean_object* v_data_2748_; 
v___x_2745_ = lean_box(v_result_2737_);
v___x_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
v___x_2747_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__0);
lean_inc_ref(v_tag_2699_);
lean_inc_ref(v___x_2746_);
lean_inc(v_cls_2697_);
v_data_2748_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2748_, 0, v_cls_2697_);
lean_ctor_set(v_data_2748_, 1, v___x_2746_);
lean_ctor_set(v_data_2748_, 2, v_tag_2699_);
lean_ctor_set_float(v_data_2748_, sizeof(void*)*3, v___x_2747_);
lean_ctor_set_float(v_data_2748_, sizeof(void*)*3 + 8, v___x_2747_);
lean_ctor_set_uint8(v_data_2748_, sizeof(void*)*3 + 16, v_collapsed_2698_);
if (v___x_2733_ == 0)
{
lean_dec_ref(v___x_2746_);
lean_dec(v_snd_2728_);
lean_dec(v_fst_2727_);
lean_dec_ref(v_tag_2699_);
lean_dec(v_cls_2697_);
v___y_2714_ = v_m_2744_;
v___y_2715_ = v___y_2735_;
v_data_2716_ = v_data_2748_;
goto v___jp_2713_;
}
else
{
lean_object* v_data_2749_; double v___x_2750_; double v___x_2751_; 
lean_dec_ref(v_data_2748_);
v_data_2749_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2749_, 0, v_cls_2697_);
lean_ctor_set(v_data_2749_, 1, v___x_2746_);
lean_ctor_set(v_data_2749_, 2, v_tag_2699_);
v___x_2750_ = lean_unbox_float(v_fst_2727_);
lean_dec(v_fst_2727_);
lean_ctor_set_float(v_data_2749_, sizeof(void*)*3, v___x_2750_);
v___x_2751_ = lean_unbox_float(v_snd_2728_);
lean_dec(v_snd_2728_);
lean_ctor_set_float(v_data_2749_, sizeof(void*)*3 + 8, v___x_2751_);
lean_ctor_set_uint8(v_data_2749_, sizeof(void*)*3 + 16, v_collapsed_2698_);
v___y_2714_ = v_m_2744_;
v___y_2715_ = v___y_2735_;
v_data_2716_ = v_data_2749_;
goto v___jp_2713_;
}
}
}
}
v___jp_2754_:
{
lean_object* v_ref_2755_; lean_object* v___x_2756_; 
v_ref_2755_ = lean_ctor_get(v___y_2705_, 5);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v_fst_2708_);
v___x_2756_ = lean_apply_4(v_msg_2703_, v_fst_2708_, v___y_2705_, v___y_2706_, lean_box(0));
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref(v___x_2756_);
v___y_2735_ = v_ref_2755_;
v_a_2736_ = v_a_2757_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2758_; 
lean_dec_ref(v___x_2756_);
v___x_2758_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3);
v___y_2735_ = v_ref_2755_;
v_a_2736_ = v___x_2758_;
goto v___jp_2734_;
}
}
v___jp_2759_:
{
if (v_clsEnabled_2701_ == 0)
{
if (v___y_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v_traceState_2762_; lean_object* v_env_2763_; lean_object* v_nextMacroScope_2764_; lean_object* v_ngen_2765_; lean_object* v_auxDeclNGen_2766_; lean_object* v_cache_2767_; lean_object* v_messages_2768_; lean_object* v_infoState_2769_; lean_object* v_snapshotTasks_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2789_; 
lean_del_object(v___x_2730_);
lean_dec(v_snd_2728_);
lean_dec(v_fst_2727_);
lean_del_object(v___x_2711_);
lean_dec_ref(v_msg_2703_);
lean_dec_ref(v_tag_2699_);
lean_dec(v_cls_2697_);
v___x_2761_ = lean_st_ref_take(v___y_2706_);
v_traceState_2762_ = lean_ctor_get(v___x_2761_, 4);
v_env_2763_ = lean_ctor_get(v___x_2761_, 0);
v_nextMacroScope_2764_ = lean_ctor_get(v___x_2761_, 1);
v_ngen_2765_ = lean_ctor_get(v___x_2761_, 2);
v_auxDeclNGen_2766_ = lean_ctor_get(v___x_2761_, 3);
v_cache_2767_ = lean_ctor_get(v___x_2761_, 5);
v_messages_2768_ = lean_ctor_get(v___x_2761_, 6);
v_infoState_2769_ = lean_ctor_get(v___x_2761_, 7);
v_snapshotTasks_2770_ = lean_ctor_get(v___x_2761_, 8);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2772_ = v___x_2761_;
v_isShared_2773_ = v_isSharedCheck_2789_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_snapshotTasks_2770_);
lean_inc(v_infoState_2769_);
lean_inc(v_messages_2768_);
lean_inc(v_cache_2767_);
lean_inc(v_traceState_2762_);
lean_inc(v_auxDeclNGen_2766_);
lean_inc(v_ngen_2765_);
lean_inc(v_nextMacroScope_2764_);
lean_inc(v_env_2763_);
lean_dec(v___x_2761_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2789_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
uint64_t v_tid_2774_; lean_object* v_traces_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2788_; 
v_tid_2774_ = lean_ctor_get_uint64(v_traceState_2762_, sizeof(void*)*1);
v_traces_2775_ = lean_ctor_get(v_traceState_2762_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_traceState_2762_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2777_ = v_traceState_2762_;
v_isShared_2778_ = v_isSharedCheck_2788_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_traces_2775_);
lean_dec(v_traceState_2762_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2788_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2702_, v_traces_2775_);
lean_dec_ref(v_traces_2775_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2779_);
v___x_2781_ = v___x_2777_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2779_);
lean_ctor_set_uint64(v_reuseFailAlloc_2787_, sizeof(void*)*1, v_tid_2774_);
v___x_2781_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2783_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v___x_2781_);
v___x_2783_ = v___x_2772_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_env_2763_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_nextMacroScope_2764_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_ngen_2765_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_auxDeclNGen_2766_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2786_, 5, v_cache_2767_);
lean_ctor_set(v_reuseFailAlloc_2786_, 6, v_messages_2768_);
lean_ctor_set(v_reuseFailAlloc_2786_, 7, v_infoState_2769_);
lean_ctor_set(v_reuseFailAlloc_2786_, 8, v_snapshotTasks_2770_);
v___x_2783_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_st_ref_set(v___y_2706_, v___x_2783_);
v___x_2785_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2708_);
return v___x_2785_;
}
}
}
}
}
else
{
goto v___jp_2754_;
}
}
else
{
goto v___jp_2754_;
}
}
v___jp_2790_:
{
double v___x_2792_; double v___x_2793_; double v___x_2794_; uint8_t v___x_2795_; 
v___x_2792_ = lean_unbox_float(v_snd_2728_);
v___x_2793_ = lean_unbox_float(v_fst_2727_);
v___x_2794_ = lean_float_sub(v___x_2792_, v___x_2793_);
v___x_2795_ = lean_float_decLt(v___y_2791_, v___x_2794_);
v___y_2760_ = v___x_2795_;
goto v___jp_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_2808_, lean_object* v_collapsed_2809_, lean_object* v_tag_2810_, lean_object* v_opts_2811_, lean_object* v_clsEnabled_2812_, lean_object* v_oldTraces_2813_, lean_object* v_msg_2814_, lean_object* v_resStartStop_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
uint8_t v_collapsed_boxed_2819_; uint8_t v_clsEnabled_boxed_2820_; lean_object* v_res_2821_; 
v_collapsed_boxed_2819_ = lean_unbox(v_collapsed_2809_);
v_clsEnabled_boxed_2820_ = lean_unbox(v_clsEnabled_2812_);
v_res_2821_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_2808_, v_collapsed_boxed_2819_, v_tag_2810_, v_opts_2811_, v_clsEnabled_boxed_2820_, v_oldTraces_2813_, v_msg_2814_, v_resStartStop_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec_ref(v_opts_2811_);
return v_res_2821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
lean_ctor_set(v___x_2826_, 2, v___x_2825_);
lean_ctor_set(v___x_2826_, 3, v___x_2825_);
lean_ctor_set(v___x_2826_, 4, v___x_2824_);
lean_ctor_set(v___x_2826_, 5, v___x_2824_);
lean_ctor_set(v___x_2826_, 6, v___x_2824_);
lean_ctor_set(v___x_2826_, 7, v___x_2824_);
lean_ctor_set(v___x_2826_, 8, v___x_2824_);
lean_ctor_set(v___x_2826_, 9, v___x_2824_);
return v___x_2826_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2828_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
lean_ctor_set(v___x_2828_, 2, v___x_2827_);
lean_ctor_set(v___x_2828_, 3, v___x_2827_);
lean_ctor_set(v___x_2828_, 4, v___x_2827_);
lean_ctor_set(v___x_2828_, 5, v___x_2827_);
return v___x_2828_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
lean_ctor_set(v___x_2830_, 2, v___x_2829_);
lean_ctor_set(v___x_2830_, 3, v___x_2829_);
lean_ctor_set(v___x_2830_, 4, v___x_2829_);
return v___x_2830_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2831_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2832_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_2833_ = lean_box(1);
v___x_2834_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2835_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
lean_ctor_set(v___x_2836_, 1, v___x_2834_);
lean_ctor_set(v___x_2836_, 2, v___x_2833_);
lean_ctor_set(v___x_2836_, 3, v___x_2832_);
lean_ctor_set(v___x_2836_, 4, v___x_2831_);
return v___x_2836_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2841_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_getEqnsFor_x3f_spec__0_spec__0___closed__1));
v___x_2842_ = l_Lean_Name_append(v___x_2841_, v___x_2840_);
return v___x_2842_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2843_; double v___x_2844_; 
v___x_2843_ = lean_unsigned_to_nat(1000000000u);
v___x_2844_ = lean_float_of_nat(v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_2845_, lean_object* v_name_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_options_2850_; uint8_t v_hasTrace_2851_; 
v_options_2850_ = lean_ctor_get(v___y_2847_, 2);
v_hasTrace_2851_ = lean_ctor_get_uint8(v_options_2850_, sizeof(void*)*1);
if (v_hasTrace_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v_env_2853_; lean_object* v___x_2854_; 
lean_dec_ref(v___f_2845_);
v___x_2852_ = lean_st_ref_get(v___y_2848_);
v_env_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_ref(v_env_2853_);
lean_dec(v___x_2852_);
lean_inc(v_name_2846_);
v___x_2854_ = l_Lean_Meta_declFromEqLikeName(v_env_2853_, v_name_2846_);
if (lean_obj_tag(v___x_2854_) == 1)
{
lean_object* v_val_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2954_; 
v_val_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2954_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_val_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2954_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v_fst_2859_; lean_object* v_snd_2860_; lean_object* v___x_2861_; lean_object* v_env_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v_fst_2859_ = lean_ctor_get(v_val_2855_, 0);
lean_inc_n(v_fst_2859_, 2);
v_snd_2860_ = lean_ctor_get(v_val_2855_, 1);
lean_inc_n(v_snd_2860_, 2);
lean_dec(v_val_2855_);
v___x_2861_ = lean_st_ref_get(v___y_2848_);
v_env_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc_ref(v_env_2862_);
lean_dec(v___x_2861_);
v___x_2863_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2862_, v_fst_2859_, v_snd_2860_);
v___x_2864_ = lean_name_eq(v_name_2846_, v___x_2863_);
lean_dec(v___x_2863_);
lean_dec(v_name_2846_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2867_; 
lean_dec(v_snd_2860_);
lean_dec(v_fst_2859_);
v___x_2865_ = lean_box(v_hasTrace_2851_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set_tag(v___x_2857_, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2865_);
v___x_2867_ = v___x_2857_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
else
{
uint8_t v___x_2869_; lean_object* v_a_2871_; 
lean_inc(v_snd_2860_);
v___x_2869_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_2860_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2885_; uint8_t v___x_2886_; lean_object* v_a_2888_; 
lean_del_object(v___x_2857_);
v___x_2885_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_2886_ = lean_string_dec_eq(v_snd_2860_, v___x_2885_);
lean_dec(v_snd_2860_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_dec(v_fst_2859_);
v___x_2900_ = lean_box(v_hasTrace_2851_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
else
{
uint8_t v___x_2902_; uint8_t v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; uint64_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2902_ = 1;
v___x_2903_ = 0;
v___x_2904_ = 2;
v___x_2905_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2905_, 0, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2905_, 1, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2905_, 2, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2905_, 3, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2905_, 4, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2905_, 5, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 6, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 7, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2905_, 8, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 9, v___x_2902_);
lean_ctor_set_uint8(v___x_2905_, 10, v___x_2903_);
lean_ctor_set_uint8(v___x_2905_, 11, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 12, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 13, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 14, v___x_2904_);
lean_ctor_set_uint8(v___x_2905_, 15, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 16, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 17, v___x_2886_);
lean_ctor_set_uint8(v___x_2905_, 18, v___x_2886_);
v___x_2906_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2905_);
v___x_2907_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set_uint64(v___x_2907_, sizeof(void*)*1, v___x_2906_);
v___x_2908_ = lean_box(1);
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2911_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2913_, 0, v___x_2907_);
lean_ctor_set(v___x_2913_, 1, v___x_2908_);
lean_ctor_set(v___x_2913_, 2, v___x_2910_);
lean_ctor_set(v___x_2913_, 3, v___x_2911_);
lean_ctor_set(v___x_2913_, 4, v___x_2912_);
lean_ctor_set(v___x_2913_, 5, v___x_2909_);
lean_ctor_set(v___x_2913_, 6, v___x_2912_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*7, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*7 + 1, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*7 + 2, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*7 + 3, v___x_2864_);
v___x_2914_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2915_ = lean_st_mk_ref(v___x_2914_);
v___x_2916_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_2859_, v___x_2864_, v___x_2913_, v___x_2915_, v___y_2847_, v___y_2848_);
lean_dec_ref(v___x_2913_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref(v___x_2916_);
v___x_2918_ = lean_st_ref_get(v___x_2915_);
lean_dec(v___x_2915_);
lean_dec(v___x_2918_);
v_a_2888_ = v_a_2917_;
goto v___jp_2887_;
}
else
{
lean_dec(v___x_2915_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2919_; 
v_a_2919_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2919_);
lean_dec_ref(v___x_2916_);
v_a_2888_ = v_a_2919_;
goto v___jp_2887_;
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
v_a_2920_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2916_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2916_);
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
}
v___jp_2887_:
{
if (lean_obj_tag(v_a_2888_) == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_box(v_hasTrace_2851_);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
else
{
lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2898_; 
v_isSharedCheck_2898_ = !lean_is_exclusive(v_a_2888_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v_a_2888_, 0);
lean_dec(v_unused_2899_);
v___x_2892_ = v_a_2888_;
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
else
{
lean_dec(v_a_2888_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_box(v___x_2886_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2894_);
v___x_2896_ = v___x_2892_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
else
{
uint8_t v___x_2928_; uint8_t v___x_2929_; uint8_t v___x_2930_; lean_object* v___x_2931_; uint64_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec(v_snd_2860_);
v___x_2928_ = 1;
v___x_2929_ = 0;
v___x_2930_ = 2;
v___x_2931_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2931_, 0, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2931_, 1, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2931_, 2, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2931_, 3, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2931_, 4, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2931_, 5, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 6, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 7, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2931_, 8, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 9, v___x_2928_);
lean_ctor_set_uint8(v___x_2931_, 10, v___x_2929_);
lean_ctor_set_uint8(v___x_2931_, 11, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 12, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 13, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 14, v___x_2930_);
lean_ctor_set_uint8(v___x_2931_, 15, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 16, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 17, v___x_2869_);
lean_ctor_set_uint8(v___x_2931_, 18, v___x_2869_);
v___x_2932_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2931_);
v___x_2933_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2933_, 0, v___x_2931_);
lean_ctor_set_uint64(v___x_2933_, sizeof(void*)*1, v___x_2932_);
v___x_2934_ = lean_box(1);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2937_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2939_, 0, v___x_2933_);
lean_ctor_set(v___x_2939_, 1, v___x_2934_);
lean_ctor_set(v___x_2939_, 2, v___x_2936_);
lean_ctor_set(v___x_2939_, 3, v___x_2937_);
lean_ctor_set(v___x_2939_, 4, v___x_2938_);
lean_ctor_set(v___x_2939_, 5, v___x_2935_);
lean_ctor_set(v___x_2939_, 6, v___x_2938_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*7, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*7 + 1, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*7 + 2, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*7 + 3, v___x_2864_);
v___x_2940_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2941_ = lean_st_mk_ref(v___x_2940_);
v___x_2942_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_2859_, v___x_2939_, v___x_2941_, v___y_2847_, v___y_2848_);
lean_dec_ref(v___x_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = lean_st_ref_get(v___x_2941_);
lean_dec(v___x_2941_);
lean_dec(v___x_2944_);
v_a_2871_ = v_a_2943_;
goto v___jp_2870_;
}
else
{
lean_dec(v___x_2941_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2945_; 
v_a_2945_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2942_);
v_a_2871_ = v_a_2945_;
goto v___jp_2870_;
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_del_object(v___x_2857_);
v_a_2946_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2942_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2942_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
v___jp_2870_:
{
if (lean_obj_tag(v_a_2871_) == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = lean_box(v_hasTrace_2851_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set_tag(v___x_2857_, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2872_);
v___x_2874_ = v___x_2857_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
else
{
lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2883_; 
lean_del_object(v___x_2857_);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_a_2871_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v_a_2871_, 0);
lean_dec(v_unused_2884_);
v___x_2877_ = v_a_2871_;
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
else
{
lean_dec(v_a_2871_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = lean_box(v___x_2869_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set_tag(v___x_2877_, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2879_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v___x_2854_);
lean_dec(v_name_2846_);
v___x_2955_ = lean_box(v_hasTrace_2851_);
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2957_; lean_object* v___f_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v_a_2966_; lean_object* v___y_2979_; lean_object* v___y_2980_; uint8_t v_a_2981_; lean_object* v___y_2985_; uint8_t v___y_2986_; lean_object* v___y_2987_; lean_object* v_a_2988_; lean_object* v___y_2990_; uint8_t v___y_2991_; lean_object* v___y_2992_; lean_object* v_a_2993_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v_a_2997_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v_a_3002_; lean_object* v___y_3012_; lean_object* v___y_3013_; uint8_t v_a_3014_; lean_object* v___y_3018_; uint8_t v___y_3019_; uint8_t v___y_3020_; lean_object* v___y_3021_; lean_object* v_a_3022_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3026_; lean_object* v_a_3027_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v_a_3032_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; 
v_inheritedTraceOptions_2957_ = lean_ctor_get(v___y_2847_, 13);
lean_inc(v_name_2846_);
v___f_2958_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_2958_, 0, v_name_2846_);
v___x_2959_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2960_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_generateEagerEqns_spec__1___closed__1));
v___x_2961_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2962_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2957_, v_options_2850_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v_a_3160_; lean_object* v_a_3173_; 
v___x_3157_ = l_Lean_trace_profiler;
v___x_3158_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_2850_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3185_; lean_object* v_env_3186_; lean_object* v___x_3187_; 
lean_dec_ref(v___f_2958_);
lean_dec_ref(v___f_2845_);
v___x_3185_ = lean_st_ref_get(v___y_2848_);
v_env_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc_ref(v_env_3186_);
lean_dec(v___x_3185_);
lean_inc(v_name_2846_);
v___x_3187_ = l_Lean_Meta_declFromEqLikeName(v_env_3186_, v_name_2846_);
if (lean_obj_tag(v___x_3187_) == 1)
{
lean_object* v_val_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3261_; 
v_val_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3261_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_val_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3261_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v_fst_3192_; lean_object* v_snd_3193_; lean_object* v___x_3194_; lean_object* v_env_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v_fst_3192_ = lean_ctor_get(v_val_3188_, 0);
lean_inc_n(v_fst_3192_, 2);
v_snd_3193_ = lean_ctor_get(v_val_3188_, 1);
lean_inc_n(v_snd_3193_, 2);
lean_dec(v_val_3188_);
v___x_3194_ = lean_st_ref_get(v___y_2848_);
v_env_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc_ref(v_env_3195_);
lean_dec(v___x_3194_);
v___x_3196_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3195_, v_fst_3192_, v_snd_3193_);
v___x_3197_ = lean_name_eq(v_name_2846_, v___x_3196_);
lean_dec(v___x_3196_);
lean_dec(v_name_2846_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
lean_dec(v_snd_3193_);
lean_dec(v_fst_3192_);
v___x_3198_ = lean_box(v___x_3158_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set_tag(v___x_3190_, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3198_);
v___x_3200_ = v___x_3190_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
else
{
uint8_t v___x_3202_; 
lean_inc(v_snd_3193_);
v___x_3202_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3193_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3203_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3204_ = lean_string_dec_eq(v_snd_3193_, v___x_3203_);
lean_dec(v_snd_3193_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
lean_dec(v_fst_3192_);
v___x_3205_ = lean_box(v___x_3158_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set_tag(v___x_3190_, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3205_);
v___x_3207_ = v___x_3190_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
else
{
uint8_t v___x_3209_; uint8_t v___x_3210_; uint8_t v___x_3211_; lean_object* v___x_3212_; uint64_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_del_object(v___x_3190_);
v___x_3209_ = 1;
v___x_3210_ = 0;
v___x_3211_ = 2;
v___x_3212_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3212_, 0, v___x_3158_);
lean_ctor_set_uint8(v___x_3212_, 1, v___x_3158_);
lean_ctor_set_uint8(v___x_3212_, 2, v___x_3158_);
lean_ctor_set_uint8(v___x_3212_, 3, v___x_3158_);
lean_ctor_set_uint8(v___x_3212_, 4, v___x_3158_);
lean_ctor_set_uint8(v___x_3212_, 5, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 6, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 7, v___x_3158_);
lean_ctor_set_uint8(v___x_3212_, 8, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 9, v___x_3209_);
lean_ctor_set_uint8(v___x_3212_, 10, v___x_3210_);
lean_ctor_set_uint8(v___x_3212_, 11, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 12, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 13, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 14, v___x_3211_);
lean_ctor_set_uint8(v___x_3212_, 15, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 16, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 17, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3212_, 18, v_hasTrace_2851_);
v___x_3213_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3212_);
v___x_3214_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set_uint64(v___x_3214_, sizeof(void*)*1, v___x_3213_);
v___x_3215_ = lean_box(1);
v___x_3216_ = lean_unsigned_to_nat(0u);
v___x_3217_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3219_ = lean_box(0);
v___x_3220_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3220_, 0, v___x_3214_);
lean_ctor_set(v___x_3220_, 1, v___x_3215_);
lean_ctor_set(v___x_3220_, 2, v___x_3217_);
lean_ctor_set(v___x_3220_, 3, v___x_3218_);
lean_ctor_set(v___x_3220_, 4, v___x_3219_);
lean_ctor_set(v___x_3220_, 5, v___x_3216_);
lean_ctor_set(v___x_3220_, 6, v___x_3219_);
lean_ctor_set_uint8(v___x_3220_, sizeof(void*)*7, v___x_3158_);
lean_ctor_set_uint8(v___x_3220_, sizeof(void*)*7 + 1, v___x_3158_);
lean_ctor_set_uint8(v___x_3220_, sizeof(void*)*7 + 2, v___x_3158_);
lean_ctor_set_uint8(v___x_3220_, sizeof(void*)*7 + 3, v_hasTrace_2851_);
v___x_3221_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3222_ = lean_st_mk_ref(v___x_3221_);
v___x_3223_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3192_, v_hasTrace_2851_, v___x_3220_, v___x_3222_, v___y_2847_, v___y_2848_);
lean_dec_ref(v___x_3220_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3225_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref(v___x_3223_);
v___x_3225_ = lean_st_ref_get(v___x_3222_);
lean_dec(v___x_3222_);
lean_dec(v___x_3225_);
v_a_3173_ = v_a_3224_;
goto v___jp_3172_;
}
else
{
lean_dec(v___x_3222_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3226_; 
v_a_3226_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3226_);
lean_dec_ref(v___x_3223_);
v_a_3173_ = v_a_3226_;
goto v___jp_3172_;
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
v_a_3227_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3223_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3223_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
}
else
{
uint8_t v___x_3235_; uint8_t v___x_3236_; uint8_t v___x_3237_; lean_object* v___x_3238_; uint64_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_dec(v_snd_3193_);
lean_del_object(v___x_3190_);
v___x_3235_ = 1;
v___x_3236_ = 0;
v___x_3237_ = 2;
v___x_3238_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3238_, 0, v___x_3158_);
lean_ctor_set_uint8(v___x_3238_, 1, v___x_3158_);
lean_ctor_set_uint8(v___x_3238_, 2, v___x_3158_);
lean_ctor_set_uint8(v___x_3238_, 3, v___x_3158_);
lean_ctor_set_uint8(v___x_3238_, 4, v___x_3158_);
lean_ctor_set_uint8(v___x_3238_, 5, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 6, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 7, v___x_3158_);
lean_ctor_set_uint8(v___x_3238_, 8, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 9, v___x_3235_);
lean_ctor_set_uint8(v___x_3238_, 10, v___x_3236_);
lean_ctor_set_uint8(v___x_3238_, 11, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 12, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 13, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 14, v___x_3237_);
lean_ctor_set_uint8(v___x_3238_, 15, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 16, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 17, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3238_, 18, v_hasTrace_2851_);
v___x_3239_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3238_);
v___x_3240_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3240_, 0, v___x_3238_);
lean_ctor_set_uint64(v___x_3240_, sizeof(void*)*1, v___x_3239_);
v___x_3241_ = lean_box(1);
v___x_3242_ = lean_unsigned_to_nat(0u);
v___x_3243_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3244_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3246_, 0, v___x_3240_);
lean_ctor_set(v___x_3246_, 1, v___x_3241_);
lean_ctor_set(v___x_3246_, 2, v___x_3243_);
lean_ctor_set(v___x_3246_, 3, v___x_3244_);
lean_ctor_set(v___x_3246_, 4, v___x_3245_);
lean_ctor_set(v___x_3246_, 5, v___x_3242_);
lean_ctor_set(v___x_3246_, 6, v___x_3245_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*7, v___x_3158_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*7 + 1, v___x_3158_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*7 + 2, v___x_3158_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*7 + 3, v_hasTrace_2851_);
v___x_3247_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3248_ = lean_st_mk_ref(v___x_3247_);
v___x_3249_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3192_, v___x_3246_, v___x_3248_, v___y_2847_, v___y_2848_);
lean_dec_ref(v___x_3246_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3251_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = lean_st_ref_get(v___x_3248_);
lean_dec(v___x_3248_);
lean_dec(v___x_3251_);
v_a_3160_ = v_a_3250_;
goto v___jp_3159_;
}
else
{
lean_dec(v___x_3248_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3252_; 
v_a_3252_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3249_);
v_a_3160_ = v_a_3252_;
goto v___jp_3159_;
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
v_a_3253_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3249_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3249_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
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
lean_object* v___x_3262_; lean_object* v___x_3263_; 
lean_dec(v___x_3187_);
lean_dec(v_name_2846_);
v___x_3262_ = lean_box(v___x_3158_);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
return v___x_3263_;
}
}
else
{
goto v___jp_3041_;
}
v___jp_3159_:
{
if (lean_obj_tag(v_a_3160_) == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_box(v___x_3158_);
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
else
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3170_; 
v_isSharedCheck_3170_ = !lean_is_exclusive(v_a_3160_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v_a_3160_, 0);
lean_dec(v_unused_3171_);
v___x_3164_ = v_a_3160_;
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v_a_3160_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = lean_box(v_hasTrace_2851_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set_tag(v___x_3164_, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3166_);
v___x_3168_ = v___x_3164_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
v___jp_3172_:
{
if (lean_obj_tag(v_a_3173_) == 0)
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_box(v___x_3158_);
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
else
{
lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3183_; 
v_isSharedCheck_3183_ = !lean_is_exclusive(v_a_3173_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; 
v_unused_3184_ = lean_ctor_get(v_a_3173_, 0);
lean_dec(v_unused_3184_);
v___x_3177_ = v_a_3173_;
v_isShared_3178_ = v_isSharedCheck_3183_;
goto v_resetjp_3176_;
}
else
{
lean_dec(v_a_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3183_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3179_ = lean_box(v_hasTrace_2851_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set_tag(v___x_3177_, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3179_);
v___x_3181_ = v___x_3177_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
else
{
goto v___jp_3041_;
}
v___jp_2963_:
{
lean_object* v___x_2967_; double v___x_2968_; double v___x_2969_; double v___x_2970_; double v___x_2971_; double v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2967_ = lean_io_mono_nanos_now();
v___x_2968_ = lean_float_of_nat(v___y_2964_);
v___x_2969_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2970_ = lean_float_div(v___x_2968_, v___x_2969_);
v___x_2971_ = lean_float_of_nat(v___x_2967_);
v___x_2972_ = lean_float_div(v___x_2971_, v___x_2969_);
v___x_2973_ = lean_box_float(v___x_2970_);
v___x_2974_ = lean_box_float(v___x_2972_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2973_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v_a_2966_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_2959_, v_hasTrace_2851_, v___x_2960_, v_options_2850_, v___x_2962_, v___y_2965_, v___f_2958_, v___x_2976_, v___y_2847_, v___y_2848_);
return v___x_2977_;
}
v___jp_2978_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_box(v_a_2981_);
v___x_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
v___y_2964_ = v___y_2979_;
v___y_2965_ = v___y_2980_;
v_a_2966_ = v___x_2983_;
goto v___jp_2963_;
}
v___jp_2984_:
{
if (lean_obj_tag(v_a_2988_) == 0)
{
v___y_2979_ = v___y_2985_;
v___y_2980_ = v___y_2987_;
v_a_2981_ = v___y_2986_;
goto v___jp_2978_;
}
else
{
lean_dec_ref(v_a_2988_);
v___y_2979_ = v___y_2985_;
v___y_2980_ = v___y_2987_;
v_a_2981_ = v_hasTrace_2851_;
goto v___jp_2978_;
}
}
v___jp_2989_:
{
if (lean_obj_tag(v_a_2993_) == 0)
{
v___y_2979_ = v___y_2990_;
v___y_2980_ = v___y_2992_;
v_a_2981_ = v___y_2991_;
goto v___jp_2978_;
}
else
{
lean_dec_ref(v_a_2993_);
v___y_2979_ = v___y_2990_;
v___y_2980_ = v___y_2992_;
v_a_2981_ = v_hasTrace_2851_;
goto v___jp_2978_;
}
}
v___jp_2994_:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_a_2997_);
v___y_2964_ = v___y_2995_;
v___y_2965_ = v___y_2996_;
v_a_2966_ = v___x_2998_;
goto v___jp_2963_;
}
v___jp_2999_:
{
lean_object* v___x_3003_; double v___x_3004_; double v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3003_ = lean_io_get_num_heartbeats();
v___x_3004_ = lean_float_of_nat(v___y_3000_);
v___x_3005_ = lean_float_of_nat(v___x_3003_);
v___x_3006_ = lean_box_float(v___x_3004_);
v___x_3007_ = lean_box_float(v___x_3005_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3009_, 0, v_a_3002_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_2959_, v_hasTrace_2851_, v___x_2960_, v_options_2850_, v___x_2962_, v___y_3001_, v___f_2958_, v___x_3009_, v___y_2847_, v___y_2848_);
return v___x_3010_;
}
v___jp_3011_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_box(v_a_3014_);
v___x_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
v___y_3000_ = v___y_3012_;
v___y_3001_ = v___y_3013_;
v_a_3002_ = v___x_3016_;
goto v___jp_2999_;
}
v___jp_3017_:
{
if (lean_obj_tag(v_a_3022_) == 0)
{
v___y_3012_ = v___y_3018_;
v___y_3013_ = v___y_3021_;
v_a_3014_ = v___y_3020_;
goto v___jp_3011_;
}
else
{
lean_dec_ref(v_a_3022_);
v___y_3012_ = v___y_3018_;
v___y_3013_ = v___y_3021_;
v_a_3014_ = v___y_3019_;
goto v___jp_3011_;
}
}
v___jp_3023_:
{
if (lean_obj_tag(v_a_3027_) == 0)
{
uint8_t v___x_3028_; 
v___x_3028_ = 0;
v___y_3012_ = v___y_3024_;
v___y_3013_ = v___y_3026_;
v_a_3014_ = v___x_3028_;
goto v___jp_3011_;
}
else
{
lean_dec_ref(v_a_3027_);
v___y_3012_ = v___y_3024_;
v___y_3013_ = v___y_3026_;
v_a_3014_ = v___y_3025_;
goto v___jp_3011_;
}
}
v___jp_3029_:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_a_3032_);
v___y_3000_ = v___y_3030_;
v___y_3001_ = v___y_3031_;
v_a_3002_ = v___x_3033_;
goto v___jp_2999_;
}
v___jp_3034_:
{
if (lean_obj_tag(v___y_3037_) == 0)
{
lean_object* v_a_3038_; uint8_t v___x_3039_; 
v_a_3038_ = lean_ctor_get(v___y_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref(v___y_3037_);
v___x_3039_ = lean_unbox(v_a_3038_);
lean_dec(v_a_3038_);
v___y_3012_ = v___y_3035_;
v___y_3013_ = v___y_3036_;
v_a_3014_ = v___x_3039_;
goto v___jp_3011_;
}
else
{
lean_object* v_a_3040_; 
v_a_3040_ = lean_ctor_get(v___y_3037_, 0);
lean_inc(v_a_3040_);
lean_dec_ref(v___y_3037_);
v___y_3030_ = v___y_3035_;
v___y_3031_ = v___y_3036_;
v_a_3032_ = v_a_3040_;
goto v___jp_3029_;
}
}
v___jp_3041_:
{
lean_object* v___x_3042_; lean_object* v_a_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3042_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2848_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3045_ = l_Lean_Option_get___at___00Lean_Meta_getEqnsFor_x3f_spec__1(v_options_2850_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v_env_3048_; lean_object* v___x_3049_; 
lean_dec_ref(v___f_2845_);
v___x_3046_ = lean_io_mono_nanos_now();
v___x_3047_ = lean_st_ref_get(v___y_2848_);
v_env_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc_ref(v_env_3048_);
lean_dec(v___x_3047_);
lean_inc(v_name_2846_);
v___x_3049_ = l_Lean_Meta_declFromEqLikeName(v_env_3048_, v_name_2846_);
if (lean_obj_tag(v___x_3049_) == 1)
{
lean_object* v_val_3050_; lean_object* v_fst_3051_; lean_object* v_snd_3052_; lean_object* v___x_3053_; lean_object* v_env_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; 
v_val_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_val_3050_);
lean_dec_ref(v___x_3049_);
v_fst_3051_ = lean_ctor_get(v_val_3050_, 0);
lean_inc_n(v_fst_3051_, 2);
v_snd_3052_ = lean_ctor_get(v_val_3050_, 1);
lean_inc_n(v_snd_3052_, 2);
lean_dec(v_val_3050_);
v___x_3053_ = lean_st_ref_get(v___y_2848_);
v_env_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc_ref(v_env_3054_);
lean_dec(v___x_3053_);
v___x_3055_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3054_, v_fst_3051_, v_snd_3052_);
v___x_3056_ = lean_name_eq(v_name_2846_, v___x_3055_);
lean_dec(v___x_3055_);
lean_dec(v_name_2846_);
if (v___x_3056_ == 0)
{
lean_dec(v_snd_3052_);
lean_dec(v_fst_3051_);
v___y_2979_ = v___x_3046_;
v___y_2980_ = v_a_3043_;
v_a_2981_ = v___x_3045_;
goto v___jp_2978_;
}
else
{
uint8_t v___x_3057_; 
lean_inc(v_snd_3052_);
v___x_3057_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3052_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3059_ = lean_string_dec_eq(v_snd_3052_, v___x_3058_);
lean_dec(v_snd_3052_);
if (v___x_3059_ == 0)
{
lean_dec(v_fst_3051_);
v___y_2979_ = v___x_3046_;
v___y_2980_ = v_a_3043_;
v_a_2981_ = v___x_3045_;
goto v___jp_2978_;
}
else
{
uint8_t v___x_3060_; uint8_t v___x_3061_; uint8_t v___x_3062_; lean_object* v___x_3063_; uint64_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3060_ = 1;
v___x_3061_ = 0;
v___x_3062_ = 2;
v___x_3063_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3063_, 0, v___x_3045_);
lean_ctor_set_uint8(v___x_3063_, 1, v___x_3045_);
lean_ctor_set_uint8(v___x_3063_, 2, v___x_3045_);
lean_ctor_set_uint8(v___x_3063_, 3, v___x_3045_);
lean_ctor_set_uint8(v___x_3063_, 4, v___x_3045_);
lean_ctor_set_uint8(v___x_3063_, 5, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 6, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 7, v___x_3045_);
lean_ctor_set_uint8(v___x_3063_, 8, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 9, v___x_3060_);
lean_ctor_set_uint8(v___x_3063_, 10, v___x_3061_);
lean_ctor_set_uint8(v___x_3063_, 11, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 12, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 13, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 14, v___x_3062_);
lean_ctor_set_uint8(v___x_3063_, 15, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 16, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 17, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3063_, 18, v_hasTrace_2851_);
v___x_3064_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3063_);
v___x_3065_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set_uint64(v___x_3065_, sizeof(void*)*1, v___x_3064_);
v___x_3066_ = lean_box(1);
v___x_3067_ = lean_unsigned_to_nat(0u);
v___x_3068_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3069_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3071_, 0, v___x_3065_);
lean_ctor_set(v___x_3071_, 1, v___x_3066_);
lean_ctor_set(v___x_3071_, 2, v___x_3068_);
lean_ctor_set(v___x_3071_, 3, v___x_3069_);
lean_ctor_set(v___x_3071_, 4, v___x_3070_);
lean_ctor_set(v___x_3071_, 5, v___x_3067_);
lean_ctor_set(v___x_3071_, 6, v___x_3070_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*7, v___x_3045_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*7 + 1, v___x_3045_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*7 + 2, v___x_3045_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*7 + 3, v_hasTrace_2851_);
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3073_ = lean_st_mk_ref(v___x_3072_);
v___x_3074_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3051_, v_hasTrace_2851_, v___x_3071_, v___x_3073_, v___y_2847_, v___y_2848_);
lean_dec_ref(v___x_3071_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3076_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref(v___x_3074_);
v___x_3076_ = lean_st_ref_get(v___x_3073_);
lean_dec(v___x_3073_);
lean_dec(v___x_3076_);
v___y_2990_ = v___x_3046_;
v___y_2991_ = v___x_3045_;
v___y_2992_ = v_a_3043_;
v_a_2993_ = v_a_3075_;
goto v___jp_2989_;
}
else
{
lean_dec(v___x_3073_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3077_; 
v_a_3077_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3077_);
lean_dec_ref(v___x_3074_);
v___y_2990_ = v___x_3046_;
v___y_2991_ = v___x_3045_;
v___y_2992_ = v_a_3043_;
v_a_2993_ = v_a_3077_;
goto v___jp_2989_;
}
else
{
lean_object* v_a_3078_; 
v_a_3078_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3078_);
lean_dec_ref(v___x_3074_);
v___y_2995_ = v___x_3046_;
v___y_2996_ = v_a_3043_;
v_a_2997_ = v_a_3078_;
goto v___jp_2994_;
}
}
}
}
else
{
uint8_t v___x_3079_; uint8_t v___x_3080_; uint8_t v___x_3081_; lean_object* v___x_3082_; uint64_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec(v_snd_3052_);
v___x_3079_ = 1;
v___x_3080_ = 0;
v___x_3081_ = 2;
v___x_3082_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3082_, 0, v___x_3045_);
lean_ctor_set_uint8(v___x_3082_, 1, v___x_3045_);
lean_ctor_set_uint8(v___x_3082_, 2, v___x_3045_);
lean_ctor_set_uint8(v___x_3082_, 3, v___x_3045_);
lean_ctor_set_uint8(v___x_3082_, 4, v___x_3045_);
lean_ctor_set_uint8(v___x_3082_, 5, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 6, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 7, v___x_3045_);
lean_ctor_set_uint8(v___x_3082_, 8, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 9, v___x_3079_);
lean_ctor_set_uint8(v___x_3082_, 10, v___x_3080_);
lean_ctor_set_uint8(v___x_3082_, 11, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 12, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 13, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 14, v___x_3081_);
lean_ctor_set_uint8(v___x_3082_, 15, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 16, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 17, v_hasTrace_2851_);
lean_ctor_set_uint8(v___x_3082_, 18, v_hasTrace_2851_);
v___x_3083_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3082_);
v___x_3084_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set_uint64(v___x_3084_, sizeof(void*)*1, v___x_3083_);
v___x_3085_ = lean_box(1);
v___x_3086_ = lean_unsigned_to_nat(0u);
v___x_3087_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3088_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3090_, 0, v___x_3084_);
lean_ctor_set(v___x_3090_, 1, v___x_3085_);
lean_ctor_set(v___x_3090_, 2, v___x_3087_);
lean_ctor_set(v___x_3090_, 3, v___x_3088_);
lean_ctor_set(v___x_3090_, 4, v___x_3089_);
lean_ctor_set(v___x_3090_, 5, v___x_3086_);
lean_ctor_set(v___x_3090_, 6, v___x_3089_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*7, v___x_3045_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*7 + 1, v___x_3045_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*7 + 2, v___x_3045_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*7 + 3, v_hasTrace_2851_);
v___x_3091_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3092_ = lean_st_mk_ref(v___x_3091_);
v___x_3093_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3051_, v___x_3090_, v___x_3092_, v___y_2847_, v___y_2848_);
lean_dec_ref(v___x_3090_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3095_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref(v___x_3093_);
v___x_3095_ = lean_st_ref_get(v___x_3092_);
lean_dec(v___x_3092_);
lean_dec(v___x_3095_);
v___y_2985_ = v___x_3046_;
v___y_2986_ = v___x_3045_;
v___y_2987_ = v_a_3043_;
v_a_2988_ = v_a_3094_;
goto v___jp_2984_;
}
else
{
lean_dec(v___x_3092_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3096_; 
v_a_3096_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3096_);
lean_dec_ref(v___x_3093_);
v___y_2985_ = v___x_3046_;
v___y_2986_ = v___x_3045_;
v___y_2987_ = v_a_3043_;
v_a_2988_ = v_a_3096_;
goto v___jp_2984_;
}
else
{
lean_object* v_a_3097_; 
v_a_3097_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3097_);
lean_dec_ref(v___x_3093_);
v___y_2995_ = v___x_3046_;
v___y_2996_ = v_a_3043_;
v_a_2997_ = v_a_3097_;
goto v___jp_2994_;
}
}
}
}
}
else
{
lean_dec(v___x_3049_);
lean_dec(v_name_2846_);
v___y_2979_ = v___x_3046_;
v___y_2980_ = v_a_3043_;
v_a_2981_ = v___x_3045_;
goto v___jp_2978_;
}
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v_env_3100_; lean_object* v___x_3101_; 
v___x_3098_ = lean_io_get_num_heartbeats();
v___x_3099_ = lean_st_ref_get(v___y_2848_);
v_env_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc_ref(v_env_3100_);
lean_dec(v___x_3099_);
lean_inc(v_name_2846_);
v___x_3101_ = l_Lean_Meta_declFromEqLikeName(v_env_3100_, v_name_2846_);
if (lean_obj_tag(v___x_3101_) == 1)
{
lean_object* v_val_3102_; lean_object* v_fst_3103_; lean_object* v_snd_3104_; lean_object* v___x_3105_; lean_object* v_env_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v_val_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_val_3102_);
lean_dec_ref(v___x_3101_);
v_fst_3103_ = lean_ctor_get(v_val_3102_, 0);
lean_inc_n(v_fst_3103_, 2);
v_snd_3104_ = lean_ctor_get(v_val_3102_, 1);
lean_inc_n(v_snd_3104_, 2);
lean_dec(v_val_3102_);
v___x_3105_ = lean_st_ref_get(v___y_2848_);
v_env_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc_ref(v_env_3106_);
lean_dec(v___x_3105_);
v___x_3107_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3106_, v_fst_3103_, v_snd_3104_);
v___x_3108_ = lean_name_eq(v_name_2846_, v___x_3107_);
lean_dec(v___x_3107_);
lean_dec(v_name_2846_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_dec(v_snd_3104_);
lean_dec(v_fst_3103_);
v___x_3109_ = lean_box(0);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
v___x_3110_ = lean_apply_4(v___f_2845_, v___x_3109_, v___y_2847_, v___y_2848_, lean_box(0));
v___y_3035_ = v___x_3098_;
v___y_3036_ = v_a_3043_;
v___y_3037_ = v___x_3110_;
goto v___jp_3034_;
}
else
{
uint8_t v___x_3111_; 
lean_inc(v_snd_3104_);
v___x_3111_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3104_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3113_ = lean_string_dec_eq(v_snd_3104_, v___x_3112_);
lean_dec(v_snd_3104_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_dec(v_fst_3103_);
v___x_3114_ = lean_box(0);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
v___x_3115_ = lean_apply_4(v___f_2845_, v___x_3114_, v___y_2847_, v___y_2848_, lean_box(0));
v___y_3035_ = v___x_3098_;
v___y_3036_ = v_a_3043_;
v___y_3037_ = v___x_3115_;
goto v___jp_3034_;
}
else
{
uint8_t v___x_3116_; uint8_t v___x_3117_; uint8_t v___x_3118_; lean_object* v___x_3119_; uint64_t v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec_ref(v___f_2845_);
v___x_3116_ = 1;
v___x_3117_ = 0;
v___x_3118_ = 2;
v___x_3119_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3119_, 0, v___x_3111_);
lean_ctor_set_uint8(v___x_3119_, 1, v___x_3111_);
lean_ctor_set_uint8(v___x_3119_, 2, v___x_3111_);
lean_ctor_set_uint8(v___x_3119_, 3, v___x_3111_);
lean_ctor_set_uint8(v___x_3119_, 4, v___x_3111_);
lean_ctor_set_uint8(v___x_3119_, 5, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 6, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 7, v___x_3111_);
lean_ctor_set_uint8(v___x_3119_, 8, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 9, v___x_3116_);
lean_ctor_set_uint8(v___x_3119_, 10, v___x_3117_);
lean_ctor_set_uint8(v___x_3119_, 11, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 12, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 13, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 14, v___x_3118_);
lean_ctor_set_uint8(v___x_3119_, 15, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 16, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 17, v___x_3045_);
lean_ctor_set_uint8(v___x_3119_, 18, v___x_3045_);
v___x_3120_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3119_);
v___x_3121_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set_uint64(v___x_3121_, sizeof(void*)*1, v___x_3120_);
v___x_3122_ = lean_box(1);
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3125_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3126_ = lean_box(0);
v___x_3127_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3127_, 0, v___x_3121_);
lean_ctor_set(v___x_3127_, 1, v___x_3122_);
lean_ctor_set(v___x_3127_, 2, v___x_3124_);
lean_ctor_set(v___x_3127_, 3, v___x_3125_);
lean_ctor_set(v___x_3127_, 4, v___x_3126_);
lean_ctor_set(v___x_3127_, 5, v___x_3123_);
lean_ctor_set(v___x_3127_, 6, v___x_3126_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*7, v___x_3111_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*7 + 1, v___x_3111_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*7 + 2, v___x_3111_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*7 + 3, v___x_3045_);
v___x_3128_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3129_ = lean_st_mk_ref(v___x_3128_);
v___x_3130_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3103_, v___x_3045_, v___x_3127_, v___x_3129_, v___y_2847_, v___y_2848_);
lean_dec_ref(v___x_3127_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref(v___x_3130_);
v___x_3132_ = lean_st_ref_get(v___x_3129_);
lean_dec(v___x_3129_);
lean_dec(v___x_3132_);
v___y_3018_ = v___x_3098_;
v___y_3019_ = v___x_3045_;
v___y_3020_ = v___x_3111_;
v___y_3021_ = v_a_3043_;
v_a_3022_ = v_a_3131_;
goto v___jp_3017_;
}
else
{
lean_dec(v___x_3129_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3133_; 
v_a_3133_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3133_);
lean_dec_ref(v___x_3130_);
v___y_3018_ = v___x_3098_;
v___y_3019_ = v___x_3045_;
v___y_3020_ = v___x_3111_;
v___y_3021_ = v_a_3043_;
v_a_3022_ = v_a_3133_;
goto v___jp_3017_;
}
else
{
lean_object* v_a_3134_; 
v_a_3134_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3134_);
lean_dec_ref(v___x_3130_);
v___y_3030_ = v___x_3098_;
v___y_3031_ = v_a_3043_;
v_a_3032_ = v_a_3134_;
goto v___jp_3029_;
}
}
}
}
else
{
uint8_t v___x_3135_; uint8_t v___x_3136_; uint8_t v___x_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; uint64_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v_snd_3104_);
lean_dec_ref(v___f_2845_);
v___x_3135_ = 0;
v___x_3136_ = 1;
v___x_3137_ = 0;
v___x_3138_ = 2;
v___x_3139_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3139_, 0, v___x_3135_);
lean_ctor_set_uint8(v___x_3139_, 1, v___x_3135_);
lean_ctor_set_uint8(v___x_3139_, 2, v___x_3135_);
lean_ctor_set_uint8(v___x_3139_, 3, v___x_3135_);
lean_ctor_set_uint8(v___x_3139_, 4, v___x_3135_);
lean_ctor_set_uint8(v___x_3139_, 5, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 6, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 7, v___x_3135_);
lean_ctor_set_uint8(v___x_3139_, 8, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 9, v___x_3136_);
lean_ctor_set_uint8(v___x_3139_, 10, v___x_3137_);
lean_ctor_set_uint8(v___x_3139_, 11, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 12, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 13, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 14, v___x_3138_);
lean_ctor_set_uint8(v___x_3139_, 15, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 16, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 17, v___x_3045_);
lean_ctor_set_uint8(v___x_3139_, 18, v___x_3045_);
v___x_3140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3139_);
v___x_3141_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3141_, 0, v___x_3139_);
lean_ctor_set_uint64(v___x_3141_, sizeof(void*)*1, v___x_3140_);
v___x_3142_ = lean_box(1);
v___x_3143_ = lean_unsigned_to_nat(0u);
v___x_3144_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3145_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3147_, 0, v___x_3141_);
lean_ctor_set(v___x_3147_, 1, v___x_3142_);
lean_ctor_set(v___x_3147_, 2, v___x_3144_);
lean_ctor_set(v___x_3147_, 3, v___x_3145_);
lean_ctor_set(v___x_3147_, 4, v___x_3146_);
lean_ctor_set(v___x_3147_, 5, v___x_3143_);
lean_ctor_set(v___x_3147_, 6, v___x_3146_);
lean_ctor_set_uint8(v___x_3147_, sizeof(void*)*7, v___x_3135_);
lean_ctor_set_uint8(v___x_3147_, sizeof(void*)*7 + 1, v___x_3135_);
lean_ctor_set_uint8(v___x_3147_, sizeof(void*)*7 + 2, v___x_3135_);
lean_ctor_set_uint8(v___x_3147_, sizeof(void*)*7 + 3, v___x_3045_);
v___x_3148_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3149_ = lean_st_mk_ref(v___x_3148_);
v___x_3150_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3103_, v___x_3147_, v___x_3149_, v___y_2847_, v___y_2848_);
lean_dec_ref(v___x_3147_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3152_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref(v___x_3150_);
v___x_3152_ = lean_st_ref_get(v___x_3149_);
lean_dec(v___x_3149_);
lean_dec(v___x_3152_);
v___y_3024_ = v___x_3098_;
v___y_3025_ = v___x_3045_;
v___y_3026_ = v_a_3043_;
v_a_3027_ = v_a_3151_;
goto v___jp_3023_;
}
else
{
lean_dec(v___x_3149_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3153_; 
v_a_3153_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3150_);
v___y_3024_ = v___x_3098_;
v___y_3025_ = v___x_3045_;
v___y_3026_ = v_a_3043_;
v_a_3027_ = v_a_3153_;
goto v___jp_3023_;
}
else
{
lean_object* v_a_3154_; 
v_a_3154_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3154_);
lean_dec_ref(v___x_3150_);
v___y_3030_ = v___x_3098_;
v___y_3031_ = v_a_3043_;
v_a_3032_ = v_a_3154_;
goto v___jp_3029_;
}
}
}
}
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_dec(v___x_3101_);
lean_dec(v_name_2846_);
v___x_3155_ = lean_box(0);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
v___x_3156_ = lean_apply_4(v___f_2845_, v___x_3155_, v___y_2847_, v___y_2848_, lean_box(0));
v___y_3035_ = v___x_3098_;
v___y_3036_ = v_a_3043_;
v___y_3037_ = v___x_3156_;
goto v___jp_3034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3264_, lean_object* v_name_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3264_, v_name_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
return v_res_3269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = lean_unsigned_to_nat(3137104340u);
v___x_3314_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3315_ = l_Lean_Name_num___override(v___x_3314_, v___x_3313_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3318_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3319_ = l_Lean_Name_str___override(v___x_3318_, v___x_3317_);
return v___x_3319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3322_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3323_ = l_Lean_Name_str___override(v___x_3322_, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = lean_unsigned_to_nat(2u);
v___x_3325_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3326_ = l_Lean_Name_num___override(v___x_3325_, v___x_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3328_; lean_object* v___x_3329_; 
v___f_3328_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3329_ = l_Lean_registerReservedNameAction(v___f_3328_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec_ref(v___x_3329_);
v___x_3330_ = ((lean_object*)(l_Lean_Meta_generateEagerEqns___closed__3));
v___x_3331_ = 0;
v___x_3332_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3333_ = l_Lean_registerTraceClass(v___x_3330_, v___x_3331_, v___x_3332_);
return v___x_3333_;
}
else
{
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b1_3336_, lean_object* v_x_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_3337_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_00_u03b1_3342_, lean_object* v_x_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b1_3342_, v_x_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3347_;
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
