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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
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
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eqnOptionsExt"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 76, 144, 60, 245, 252, 84, 163)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqnOptionsExt;
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withEqnOptions___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Meta_withEqnOptions___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Meta_withEqnOptions___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_withEqnOptions___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_withEqnOptions___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_saveEqnAffectingOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__0 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__0_value;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Meta_saveEqnAffectingOptions___closed__1;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__2;
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__3 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__3_value;
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__4 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__4_value;
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__4_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Meta_saveEqnAffectingOptions___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 70, 141, 178, 157, 107, 140, 91)}};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__5 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__5_value;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__6;
static const lean_string_object l_Lean_Meta_saveEqnAffectingOptions___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "saving equation-affecting options for "};
static const lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__7 = (const lean_object*)&l_Lean_Meta_saveEqnAffectingOptions___closed__7_value;
static lean_once_cell_t l_Lean_Meta_saveEqnAffectingOptions___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_saveEqnAffectingOptions___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(lean_object* v_env_99_, lean_object* v_as_100_, size_t v_i_101_, size_t v_stop_102_, lean_object* v_b_103_){
_start:
{
lean_object* v___y_105_; uint8_t v___x_109_; 
v___x_109_ = lean_usize_dec_eq(v_i_101_, v_stop_102_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v_fst_111_; uint8_t v___x_112_; 
v___x_110_ = lean_array_uget_borrowed(v_as_100_, v_i_101_);
v_fst_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_fst_111_);
lean_inc_ref(v_env_99_);
v___x_112_ = l_Lean_Environment_contains(v_env_99_, v_fst_111_, v___x_109_);
if (v___x_112_ == 0)
{
v___y_105_ = v_b_103_;
goto v___jp_104_;
}
else
{
lean_object* v___x_113_; 
lean_inc(v___x_110_);
v___x_113_ = lean_array_push(v_b_103_, v___x_110_);
v___y_105_ = v___x_113_;
goto v___jp_104_;
}
}
else
{
lean_dec_ref(v_env_99_);
return v_b_103_;
}
v___jp_104_:
{
size_t v___x_106_; size_t v___x_107_; 
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_101_, v___x_106_);
v_i_101_ = v___x_107_;
v_b_103_ = v___y_105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_114_, lean_object* v_as_115_, lean_object* v_i_116_, lean_object* v_stop_117_, lean_object* v_b_118_){
_start:
{
size_t v_i_boxed_119_; size_t v_stop_boxed_120_; lean_object* v_res_121_; 
v_i_boxed_119_ = lean_unbox_usize(v_i_116_);
lean_dec(v_i_116_);
v_stop_boxed_120_ = lean_unbox_usize(v_stop_117_);
lean_dec(v_stop_117_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_114_, v_as_115_, v_i_boxed_119_, v_stop_boxed_120_, v_b_118_);
lean_dec_ref(v_as_115_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_122_, lean_object* v_x_123_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v_k_124_; lean_object* v_v_125_; lean_object* v_l_126_; lean_object* v_r_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_k_124_ = lean_ctor_get(v_x_123_, 1);
v_v_125_ = lean_ctor_get(v_x_123_, 2);
v_l_126_ = lean_ctor_get(v_x_123_, 3);
v_r_127_ = lean_ctor_get(v_x_123_, 4);
v___x_128_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_122_, v_l_126_);
lean_inc(v_v_125_);
lean_inc(v_k_124_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_k_124_);
lean_ctor_set(v___x_129_, 1, v_v_125_);
v___x_130_ = lean_array_push(v___x_128_, v___x_129_);
v_init_122_ = v___x_130_;
v_x_123_ = v_r_127_;
goto _start;
}
else
{
return v_init_122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_132_, v_x_133_);
lean_dec(v_x_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(lean_object* v_env_141_, lean_object* v_s_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_145_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v___x_144_, v_s_142_);
v___x_146_ = lean_array_get_size(v___x_145_);
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_148_ = lean_nat_dec_lt(v___x_143_, v___x_146_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
lean_dec_ref(v___x_145_);
lean_dec_ref(v_env_141_);
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_le(v___x_146_, v___x_146_);
if (v___x_150_ == 0)
{
if (v___x_148_ == 0)
{
lean_object* v___x_151_; 
lean_dec_ref(v___x_145_);
lean_dec_ref(v_env_141_);
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
return v___x_151_;
}
else
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = ((size_t)0ULL);
v___x_153_ = lean_usize_of_nat(v___x_146_);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_141_, v___x_145_, v___x_152_, v___x_153_, v___x_147_);
lean_dec_ref(v___x_145_);
lean_inc_ref_n(v___x_154_, 2);
v___x_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
lean_ctor_set(v___x_155_, 2, v___x_154_);
return v___x_155_;
}
}
else
{
size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = ((size_t)0ULL);
v___x_157_ = lean_usize_of_nat(v___x_146_);
v___x_158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_141_, v___x_145_, v___x_156_, v___x_157_, v___x_147_);
lean_dec_ref(v___x_145_);
lean_inc_ref_n(v___x_158_, 2);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
lean_ctor_set(v___x_159_, 2, v___x_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_env_160_, lean_object* v_s_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(v_env_160_, v_s_161_);
lean_dec(v_s_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___f_170_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_171_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_172_ = lean_box(1);
v___x_173_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_171_, v___x_172_, v___f_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(lean_object* v_init_176_, lean_object* v_t_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_176_, v_t_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_179_, lean_object* v_t_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(v_init_179_, v_t_180_);
lean_dec(v_t_180_);
return v_res_181_;
}
}
static lean_object* _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_189_ = lean_string_utf8_byte_size(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_192_ = lean_string_utf8_byte_size(v_s_190_);
v___x_193_ = lean_obj_once(&l_Lean_Meta_isEqnReservedNameSuffix___closed__0, &l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0);
v___x_194_ = lean_nat_dec_le(v___x_193_, v___x_192_);
if (v___x_194_ == 0)
{
lean_dec_ref(v_s_190_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_string_memcmp(v_s_190_, v___x_191_, v___x_195_, v___x_195_, v___x_193_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_s_190_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_197_ = lean_unsigned_to_nat(3u);
lean_inc_ref(v_s_190_);
v___x_198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_198_, 0, v_s_190_);
lean_ctor_set(v___x_198_, 1, v___x_195_);
lean_ctor_set(v___x_198_, 2, v___x_192_);
v___x_199_ = l_String_Slice_Pos_nextn(v___x_198_, v___x_195_, v___x_197_);
lean_dec_ref(v___x_198_);
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v_s_190_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
lean_ctor_set(v___x_200_, 2, v___x_192_);
v___x_201_ = l_String_Slice_isNat(v___x_200_);
lean_dec_ref(v___x_200_);
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_209_){
_start:
{
uint8_t v___y_211_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_214_ = lean_string_dec_eq(v_s_209_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_216_ = lean_string_dec_eq(v_s_209_, v___x_215_);
v___y_211_ = v___x_216_;
goto v___jp_210_;
}
else
{
v___y_211_ = v___x_214_;
goto v___jp_210_;
}
v___jp_210_:
{
if (v___y_211_ == 0)
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_209_);
return v___x_212_;
}
else
{
lean_dec_ref(v_s_209_);
return v___y_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_Meta_isEqnLikeSuffix(v_s_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_223_, lean_object* v_env_224_, lean_object* v_as_x27_225_, lean_object* v_b_226_){
_start:
{
if (lean_obj_tag(v_as_x27_225_) == 0)
{
lean_dec_ref(v_env_224_);
lean_dec_ref(v_str_223_);
lean_inc_ref(v_b_226_);
return v_b_226_;
}
else
{
lean_object* v_head_227_; lean_object* v_tail_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___y_232_; uint8_t v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_head_227_ = lean_ctor_get(v_as_x27_225_, 0);
v_tail_228_ = lean_ctor_get(v_as_x27_225_, 1);
v___x_229_ = lean_box(0);
v___x_230_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_238_ = 0;
lean_inc_ref(v_env_224_);
v___x_239_ = l_Lean_Environment_setExporting(v_env_224_, v___x_238_);
lean_inc(v_head_227_);
v___x_240_ = l_Lean_Environment_isSafeDefinition(v___x_239_, v_head_227_);
if (v___x_240_ == 0)
{
v___y_232_ = v___x_240_;
goto v___jp_231_;
}
else
{
uint8_t v___x_241_; 
lean_inc(v_head_227_);
lean_inc_ref(v_env_224_);
v___x_241_ = lean_is_matcher(v_env_224_, v_head_227_);
if (v___x_241_ == 0)
{
v___y_232_ = v___x_240_;
goto v___jp_231_;
}
else
{
v_as_x27_225_ = v_tail_228_;
v_b_226_ = v___x_230_;
goto _start;
}
}
v___jp_231_:
{
if (v___y_232_ == 0)
{
v_as_x27_225_ = v_tail_228_;
v_b_226_ = v___x_230_;
goto _start;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec_ref(v_env_224_);
lean_inc(v_head_227_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_head_227_);
lean_ctor_set(v___x_234_, 1, v_str_223_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_229_);
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_243_, lean_object* v_env_244_, lean_object* v_as_x27_245_, lean_object* v_b_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_243_, v_env_244_, v_as_x27_245_, v_b_246_);
lean_dec_ref(v_b_246_);
lean_dec(v_as_x27_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_248_, lean_object* v_name_249_){
_start:
{
if (lean_obj_tag(v_name_249_) == 1)
{
lean_object* v_pre_250_; lean_object* v_str_251_; uint8_t v___x_252_; 
v_pre_250_ = lean_ctor_get(v_name_249_, 0);
lean_inc(v_pre_250_);
v_str_251_ = lean_ctor_get(v_name_249_, 1);
lean_inc_ref_n(v_str_251_, 2);
lean_dec_ref(v_name_249_);
v___x_252_ = l_Lean_Meta_isEqnLikeSuffix(v_str_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec_ref(v_str_251_);
lean_dec(v_pre_250_);
lean_dec_ref(v_env_248_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_fst_261_; 
lean_inc(v_pre_250_);
v___x_254_ = l_Lean_privateToUserName(v_pre_250_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v_pre_250_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_box(0);
v___x_259_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_260_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_251_, v_env_248_, v___x_257_, v___x_259_);
lean_dec_ref(v___x_257_);
v_fst_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_fst_261_);
lean_dec_ref(v___x_260_);
if (lean_obj_tag(v_fst_261_) == 0)
{
return v___x_258_;
}
else
{
lean_object* v_val_262_; 
v_val_262_ = lean_ctor_get(v_fst_261_, 0);
lean_inc(v_val_262_);
lean_dec_ref(v_fst_261_);
return v_val_262_;
}
}
}
else
{
lean_object* v___x_263_; 
lean_dec(v_name_249_);
lean_dec_ref(v_env_248_);
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_264_, lean_object* v_env_265_, lean_object* v_as_266_, lean_object* v_as_x27_267_, lean_object* v_b_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_264_, v_env_265_, v_as_x27_267_, v_b_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_271_, lean_object* v_env_272_, lean_object* v_as_273_, lean_object* v_as_x27_274_, lean_object* v_b_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_271_, v_env_272_, v_as_273_, v_as_x27_274_, v_b_275_, v_a_276_);
lean_dec_ref(v_b_275_);
lean_dec(v_as_x27_274_);
lean_dec(v_as_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_278_, lean_object* v_declName_279_, lean_object* v_suffix_280_){
_start:
{
lean_object* v___x_284_; uint8_t v_isModule_285_; 
v___x_284_ = l_Lean_Environment_header(v_env_278_);
v_isModule_285_ = lean_ctor_get_uint8(v___x_284_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_284_);
if (v_isModule_285_ == 0)
{
lean_object* v_name_286_; 
lean_dec_ref(v_env_278_);
v_name_286_ = l_Lean_Name_str___override(v_declName_279_, v_suffix_280_);
return v_name_286_;
}
else
{
uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = 0;
lean_inc_ref(v_env_278_);
v___x_288_ = l_Lean_Environment_setExporting(v_env_278_, v_isModule_285_);
lean_inc(v_declName_279_);
v___x_289_ = l_Lean_Environment_find_x3f(v___x_288_, v_declName_279_, v___x_287_);
if (lean_obj_tag(v___x_289_) == 0)
{
goto v___jp_281_;
}
else
{
lean_object* v_val_290_; uint8_t v___x_291_; 
v_val_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_290_);
lean_dec_ref(v___x_289_);
v___x_291_ = l_Lean_ConstantInfo_hasValue(v_val_290_, v___x_287_);
lean_dec(v_val_290_);
if (v___x_291_ == 0)
{
goto v___jp_281_;
}
else
{
lean_object* v_name_292_; 
lean_dec_ref(v_env_278_);
v_name_292_ = l_Lean_Name_str___override(v_declName_279_, v_suffix_280_);
return v_name_292_;
}
}
}
v___jp_281_:
{
lean_object* v_name_282_; lean_object* v___x_283_; 
v_name_282_ = l_Lean_Name_str___override(v_declName_279_, v_suffix_280_);
v___x_283_ = l_Lean_mkPrivateName(v_env_278_, v_name_282_);
lean_dec_ref(v_env_278_);
return v___x_283_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_293_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
lean_ctor_set(v___x_298_, 3, v___x_297_);
lean_ctor_set(v___x_298_, 4, v___x_296_);
lean_ctor_set(v___x_298_, 5, v___x_296_);
lean_ctor_set(v___x_298_, 6, v___x_296_);
lean_ctor_set(v___x_298_, 7, v___x_296_);
lean_ctor_set(v___x_298_, 8, v___x_296_);
lean_ctor_set(v___x_298_, 9, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_unsigned_to_nat(32u);
v___x_300_ = lean_mk_empty_array_with_capacity(v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_302_ = ((size_t)5ULL);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_unsigned_to_nat(32u);
v___x_305_ = lean_mk_empty_array_with_capacity(v___x_304_);
v___x_306_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_307_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
lean_ctor_set(v___x_307_, 2, v___x_303_);
lean_ctor_set(v___x_307_, 3, v___x_303_);
lean_ctor_set_usize(v___x_307_, 4, v___x_302_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = lean_box(1);
v___x_309_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_310_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
lean_ctor_set(v___x_311_, 2, v___x_308_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; lean_object* v_env_317_; lean_object* v_options_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_316_ = lean_st_ref_get(v___y_314_);
v_env_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc_ref(v_env_317_);
lean_dec(v___x_316_);
v_options_318_ = lean_ctor_get(v___y_313_, 2);
v___x_319_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_320_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_318_);
v___x_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_321_, 0, v_env_317_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
lean_ctor_set(v___x_321_, 3, v_options_318_);
v___x_322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_msgData_312_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_ref_333_; lean_object* v___x_334_; lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_ref_333_ = lean_ctor_get(v___y_330_, 5);
v___x_334_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_329_, v___y_330_, v___y_331_);
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_343_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
lean_inc(v_ref_333_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_ref_333_);
lean_ctor_set(v___x_339_, 1, v_a_335_);
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 1);
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_348_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_358_, lean_object* v_reservedName_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_363_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_364_ = 0;
v___x_365_ = l_Lean_MessageData_ofConstName(v_declName_358_, v___x_364_);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_363_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = 1;
v___x_370_ = l_Lean_MessageData_ofConstName(v_reservedName_359_, v___x_369_);
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_368_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_373_, v___y_360_, v___y_361_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_375_, lean_object* v_reservedName_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_375_, v_reservedName_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_381_, lean_object* v_suffix_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; lean_object* v_env_387_; lean_object* v_reservedName_388_; uint8_t v___x_389_; uint8_t v___x_390_; 
v___x_386_ = lean_st_ref_get(v___y_384_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
lean_inc(v_declName_381_);
v_reservedName_388_ = l_Lean_Name_str___override(v_declName_381_, v_suffix_382_);
v___x_389_ = 1;
lean_inc(v_reservedName_388_);
v___x_390_ = l_Lean_Environment_contains(v_env_387_, v_reservedName_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_reservedName_388_);
lean_dec(v_declName_381_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_381_, v_reservedName_388_, v___y_383_, v___y_384_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_394_, lean_object* v_suffix_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_394_, v_suffix_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_400_);
v___x_405_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_400_, v___x_404_, v_a_401_, v_a_402_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v___x_405_);
v___x_406_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_400_);
v___x_407_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_400_, v___x_406_, v_a_401_, v_a_402_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v___x_407_);
v___x_408_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_409_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_400_, v___x_408_, v_a_401_, v_a_402_);
return v___x_409_;
}
else
{
lean_dec(v_declName_400_);
return v___x_407_;
}
}
else
{
lean_dec(v_declName_400_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_416_, v___y_417_, v___y_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_421_, lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_421_, v_msg_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_427_, lean_object* v_n_428_){
_start:
{
lean_object* v___x_429_; 
lean_inc(v_n_428_);
lean_inc_ref(v_env_427_);
v___x_429_ = l_Lean_Meta_declFromEqLikeName(v_env_427_, v_n_428_);
if (lean_obj_tag(v___x_429_) == 1)
{
lean_object* v_val_430_; lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_val_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_val_430_);
lean_dec_ref(v___x_429_);
v_fst_431_ = lean_ctor_get(v_val_430_, 0);
lean_inc(v_fst_431_);
v_snd_432_ = lean_ctor_get(v_val_430_, 1);
lean_inc(v_snd_432_);
lean_dec(v_val_430_);
v___x_433_ = l_Lean_Meta_mkEqLikeNameFor(v_env_427_, v_fst_431_, v_snd_432_);
v___x_434_ = lean_name_eq(v_n_428_, v___x_433_);
lean_dec(v___x_433_);
lean_dec(v_n_428_);
return v___x_434_;
}
else
{
uint8_t v___x_435_; 
lean_dec(v___x_429_);
lean_dec(v_n_428_);
lean_dec_ref(v_env_427_);
v___x_435_ = 0;
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_436_, lean_object* v_n_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_436_, v_n_437_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_442_; lean_object* v___x_443_; 
v___f_442_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_443_ = l_Lean_registerReservedNamePredicate(v___f_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_box(0);
v___x_448_ = lean_st_mk_ref(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_451_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_454_ = lean_mk_io_user_error(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_initializing();
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_474_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_474_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_474_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_474_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
uint8_t v___x_462_; 
v___x_462_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_dec_ref(v_f_455_);
v___x_463_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 1);
lean_ctor_set(v___x_460_, 0, v___x_463_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_467_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_468_ = lean_st_ref_take(v___x_467_);
v___x_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_469_, 0, v_f_455_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = lean_st_ref_set(v___x_467_, v___x_469_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_470_);
v___x_472_ = v___x_460_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v_f_455_);
v_a_475_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_457_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_457_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Meta_registerGetEqnsFn(v_f_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_496_; lean_object* v_env_497_; uint8_t v___x_498_; lean_object* v___x_499_; 
v___x_496_ = lean_st_ref_get(v_a_490_);
v_env_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc_ref(v_env_497_);
lean_dec(v___x_496_);
v___x_498_ = 0;
lean_inc(v_declName_486_);
v___x_499_ = l_Lean_Environment_findAsync_x3f(v_env_497_, v_declName_486_, v___x_498_);
if (lean_obj_tag(v___x_499_) == 1)
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_531_; 
v_val_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_531_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_531_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_531_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
uint8_t v_kind_504_; 
v_kind_504_ = lean_ctor_get_uint8(v_val_500_, sizeof(void*)*3);
if (v_kind_504_ == 0)
{
lean_object* v_sig_505_; lean_object* v___x_506_; lean_object* v_env_507_; uint8_t v___x_508_; 
v_sig_505_ = lean_ctor_get(v_val_500_, 1);
lean_inc_ref(v_sig_505_);
lean_dec(v_val_500_);
v___x_506_ = lean_st_ref_get(v_a_490_);
v_env_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_env_507_);
lean_dec(v___x_506_);
v___x_508_ = lean_is_matcher(v_env_507_, v_declName_486_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v_type_510_; lean_object* v___x_511_; 
lean_del_object(v___x_502_);
v___x_509_ = lean_task_get_own(v_sig_505_);
v_type_510_ = lean_ctor_get(v___x_509_, 2);
lean_inc_ref(v_type_510_);
lean_dec(v___x_509_);
v___x_511_ = l_Lean_Meta_isProp(v_type_510_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_526_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_526_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
uint8_t v___x_516_; 
v___x_516_ = lean_unbox(v_a_512_);
lean_dec(v_a_512_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_517_ = 1;
v___x_518_ = lean_box(v___x_517_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_518_);
v___x_520_ = v___x_514_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_box(v___x_508_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_522_);
v___x_524_ = v___x_514_;
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
}
else
{
return v___x_511_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec_ref(v_sig_505_);
v___x_527_ = lean_box(v___x_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 0);
lean_ctor_set(v___x_502_, 0, v___x_527_);
v___x_529_ = v___x_502_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_del_object(v___x_502_);
lean_dec(v_val_500_);
lean_dec(v_declName_486_);
goto v___jp_492_;
}
}
}
else
{
lean_dec(v___x_499_);
lean_dec(v_declName_486_);
goto v___jp_492_;
}
v___jp_492_:
{
uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = 0;
v___x_494_ = lean_box(v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
return v_res_538_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_547_);
return v_res_549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_550_; lean_object* v___f_551_; 
v___x_550_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_551_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_551_, 0, v___x_550_);
return v___f_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___f_553_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_554_ = lean_box(0);
v___x_555_ = lean_box(1);
v___x_556_ = l_Lean_registerEnvExtension___redArg(v___f_553_, v___x_554_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_559_, lean_object* v_opt_560_){
_start:
{
lean_object* v_name_561_; lean_object* v_defValue_562_; lean_object* v_map_563_; lean_object* v___x_564_; 
v_name_561_ = lean_ctor_get(v_opt_560_, 0);
v_defValue_562_ = lean_ctor_get(v_opt_560_, 1);
v_map_563_ = lean_ctor_get(v_opts_559_, 0);
v___x_564_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_563_, v_name_561_);
if (lean_obj_tag(v___x_564_) == 0)
{
uint8_t v___x_565_; 
v___x_565_ = lean_unbox(v_defValue_562_);
return v___x_565_;
}
else
{
lean_object* v_val_566_; 
v_val_566_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_566_);
lean_dec_ref(v___x_564_);
if (lean_obj_tag(v_val_566_) == 1)
{
uint8_t v_v_567_; 
v_v_567_ = lean_ctor_get_uint8(v_val_566_, 0);
lean_dec_ref(v_val_566_);
return v_v_567_;
}
else
{
uint8_t v___x_568_; 
lean_dec(v_val_566_);
v___x_568_ = lean_unbox(v_defValue_562_);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_569_, lean_object* v_opt_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_569_, v_opt_570_);
lean_dec_ref(v_opt_570_);
lean_dec_ref(v_opts_569_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_opts_573_, lean_object* v_opt_574_){
_start:
{
lean_object* v_name_575_; lean_object* v_defValue_576_; lean_object* v_map_577_; lean_object* v___x_578_; 
v_name_575_ = lean_ctor_get(v_opt_574_, 0);
v_defValue_576_ = lean_ctor_get(v_opt_574_, 1);
v_map_577_ = lean_ctor_get(v_opts_573_, 0);
v___x_578_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_577_, v_name_575_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_inc(v_defValue_576_);
return v_defValue_576_;
}
else
{
lean_object* v_val_579_; 
v_val_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_579_);
lean_dec_ref(v___x_578_);
if (lean_obj_tag(v_val_579_) == 3)
{
lean_object* v_v_580_; 
v_v_580_ = lean_ctor_get(v_val_579_, 0);
lean_inc(v_v_580_);
lean_dec_ref(v_val_579_);
return v_v_580_;
}
else
{
lean_dec(v_val_579_);
lean_inc(v_defValue_576_);
return v_defValue_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_opts_581_, lean_object* v_opt_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_581_, v_opt_582_);
lean_dec_ref(v_opt_582_);
lean_dec_ref(v_opts_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_587_, size_t v_sz_588_, size_t v_i_589_, lean_object* v_b_590_){
_start:
{
lean_object* v_a_592_; uint8_t v___x_596_; 
v___x_596_ = lean_usize_dec_lt(v_i_589_, v_sz_588_);
if (v___x_596_ == 0)
{
return v_b_590_;
}
else
{
lean_object* v_a_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v_map_600_; uint8_t v_hasTrace_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_614_; 
v_a_597_ = lean_array_uget_borrowed(v_as_587_, v_i_589_);
v_fst_598_ = lean_ctor_get(v_a_597_, 0);
v_snd_599_ = lean_ctor_get(v_a_597_, 1);
v_map_600_ = lean_ctor_get(v_b_590_, 0);
v_hasTrace_601_ = lean_ctor_get_uint8(v_b_590_, sizeof(void*)*1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_b_590_);
if (v_isSharedCheck_614_ == 0)
{
v___x_603_ = v_b_590_;
v_isShared_604_ = v_isSharedCheck_614_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_map_600_);
lean_dec(v_b_590_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_614_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; 
lean_inc(v_snd_599_);
lean_inc(v_fst_598_);
v___x_605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_598_, v_snd_599_, v_map_600_);
if (v_hasTrace_601_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_609_; 
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_607_ = l_Lean_Name_isPrefixOf(v___x_606_, v_fst_598_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_605_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*1, v___x_607_);
v_a_592_ = v___x_609_;
goto v___jp_591_;
}
}
else
{
lean_object* v___x_612_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_612_ = v___x_603_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_605_);
lean_ctor_set_uint8(v_reuseFailAlloc_613_, sizeof(void*)*1, v_hasTrace_601_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v_a_592_ = v___x_612_;
goto v___jp_591_;
}
}
}
}
v___jp_591_:
{
size_t v___x_593_; size_t v___x_594_; 
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_add(v_i_589_, v___x_593_);
v_i_589_ = v___x_594_;
v_b_590_ = v_a_592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_615_, lean_object* v_sz_616_, lean_object* v_i_617_, lean_object* v_b_618_){
_start:
{
size_t v_sz_boxed_619_; size_t v_i_boxed_620_; lean_object* v_res_621_; 
v_sz_boxed_619_ = lean_unbox_usize(v_sz_616_);
lean_dec(v_sz_616_);
v_i_boxed_620_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_as_615_, v_sz_boxed_619_, v_i_boxed_620_, v_b_618_);
lean_dec_ref(v_as_615_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_622_, lean_object* v_k_623_, uint8_t v_v_624_){
_start:
{
lean_object* v_map_625_; uint8_t v_hasTrace_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_640_; 
v_map_625_ = lean_ctor_get(v_o_622_, 0);
v_hasTrace_626_ = lean_ctor_get_uint8(v_o_622_, sizeof(void*)*1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_o_622_);
if (v_isSharedCheck_640_ == 0)
{
v___x_628_ = v_o_622_;
v_isShared_629_ = v_isSharedCheck_640_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_map_625_);
lean_dec(v_o_622_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_640_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_630_, 0, v_v_624_);
lean_inc(v_k_623_);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_623_, v___x_630_, v_map_625_);
if (v_hasTrace_626_ == 0)
{
lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_635_; 
v___x_632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_633_ = l_Lean_Name_isPrefixOf(v___x_632_, v_k_623_);
lean_dec(v_k_623_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_631_);
v___x_635_ = v___x_628_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_631_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_633_);
return v___x_635_;
}
}
else
{
lean_object* v___x_638_; 
lean_dec(v_k_623_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_631_);
v___x_638_ = v___x_628_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_631_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*1, v_hasTrace_626_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_641_, lean_object* v_k_642_, lean_object* v_v_643_){
_start:
{
uint8_t v_v_boxed_644_; lean_object* v_res_645_; 
v_v_boxed_644_ = lean_unbox(v_v_643_);
v_res_645_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_641_, v_k_642_, v_v_boxed_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_646_, lean_object* v_opt_647_, uint8_t v_val_648_){
_start:
{
lean_object* v_name_649_; lean_object* v___x_650_; 
v_name_649_ = lean_ctor_get(v_opt_647_, 0);
lean_inc(v_name_649_);
lean_dec_ref(v_opt_647_);
v___x_650_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_646_, v_name_649_, v_val_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_651_, lean_object* v_opt_652_, lean_object* v_val_653_){
_start:
{
uint8_t v_val_boxed_654_; lean_object* v_res_655_; 
v_val_boxed_654_ = lean_unbox(v_val_653_);
v_res_655_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_651_, v_opt_652_, v_val_boxed_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(lean_object* v_as_656_, size_t v_i_657_, size_t v_stop_658_, lean_object* v_b_659_){
_start:
{
uint8_t v___x_660_; 
v___x_660_ = lean_usize_dec_eq(v_i_657_, v_stop_658_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v_defValue_662_; uint8_t v___x_663_; lean_object* v___x_664_; size_t v___x_665_; size_t v___x_666_; 
v___x_661_ = lean_array_uget_borrowed(v_as_656_, v_i_657_);
v_defValue_662_ = lean_ctor_get(v___x_661_, 1);
v___x_663_ = lean_unbox(v_defValue_662_);
lean_inc(v___x_661_);
v___x_664_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_659_, v___x_661_, v___x_663_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_657_, v___x_665_);
v_i_657_ = v___x_666_;
v_b_659_ = v___x_664_;
goto _start;
}
else
{
return v_b_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(lean_object* v_as_668_, lean_object* v_i_669_, lean_object* v_stop_670_, lean_object* v_b_671_){
_start:
{
size_t v_i_boxed_672_; size_t v_stop_boxed_673_; lean_object* v_res_674_; 
v_i_boxed_672_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_stop_boxed_673_ = lean_unbox_usize(v_stop_670_);
lean_dec(v_stop_670_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v_as_668_, v_i_boxed_672_, v_stop_boxed_673_, v_b_671_);
lean_dec_ref(v_as_668_);
return v_res_674_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Array_instInhabited(lean_box(0));
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = l_Lean_Meta_eqnAffectingOptions;
v___x_682_ = lean_array_get_size(v___x_681_);
return v___x_682_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_nat_dec_lt(v___x_684_, v___x_683_);
return v___x_685_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_687_ = lean_nat_dec_le(v___x_686_, v___x_686_);
return v___x_687_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__7(void){
_start:
{
lean_object* v___x_688_; size_t v___x_689_; 
v___x_688_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_689_ = lean_usize_of_nat(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_690_, lean_object* v_act_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___y_698_; uint8_t v___y_699_; lean_object* v_fileName_700_; lean_object* v_fileMap_701_; lean_object* v_currRecDepth_702_; lean_object* v_ref_703_; lean_object* v_currNamespace_704_; lean_object* v_openDecls_705_; lean_object* v_initHeartbeats_706_; lean_object* v_maxHeartbeats_707_; lean_object* v_quotContext_708_; lean_object* v_currMacroScope_709_; lean_object* v_cancelTk_x3f_710_; uint8_t v_suppressElabErrors_711_; lean_object* v_inheritedTraceOptions_712_; lean_object* v___y_713_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_env_720_; lean_object* v___x_721_; lean_object* v_toEnvExtension_722_; lean_object* v_asyncMode_723_; lean_object* v_fileName_724_; lean_object* v_fileMap_725_; lean_object* v_options_726_; lean_object* v_currRecDepth_727_; lean_object* v_ref_728_; lean_object* v_currNamespace_729_; lean_object* v_openDecls_730_; lean_object* v_initHeartbeats_731_; lean_object* v_maxHeartbeats_732_; lean_object* v_quotContext_733_; lean_object* v_currMacroScope_734_; lean_object* v_cancelTk_x3f_735_; uint8_t v_suppressElabErrors_736_; lean_object* v_inheritedTraceOptions_737_; lean_object* v___y_739_; uint8_t v___y_740_; uint8_t v___y_741_; lean_object* v___y_763_; lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; 
v___x_718_ = lean_st_ref_get(v_a_695_);
v___x_719_ = lean_st_ref_get(v_a_695_);
v_env_720_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_env_720_);
lean_dec(v___x_718_);
v___x_721_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_722_ = lean_ctor_get(v___x_721_, 0);
v_asyncMode_723_ = lean_ctor_get(v_toEnvExtension_722_, 2);
v_fileName_724_ = lean_ctor_get(v_a_694_, 0);
v_fileMap_725_ = lean_ctor_get(v_a_694_, 1);
v_options_726_ = lean_ctor_get(v_a_694_, 2);
v_currRecDepth_727_ = lean_ctor_get(v_a_694_, 3);
v_ref_728_ = lean_ctor_get(v_a_694_, 5);
v_currNamespace_729_ = lean_ctor_get(v_a_694_, 6);
v_openDecls_730_ = lean_ctor_get(v_a_694_, 7);
v_initHeartbeats_731_ = lean_ctor_get(v_a_694_, 8);
v_maxHeartbeats_732_ = lean_ctor_get(v_a_694_, 9);
v_quotContext_733_ = lean_ctor_get(v_a_694_, 10);
v_currMacroScope_734_ = lean_ctor_get(v_a_694_, 11);
v_cancelTk_x3f_735_ = lean_ctor_get(v_a_694_, 12);
v_suppressElabErrors_736_ = lean_ctor_get_uint8(v_a_694_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_737_ = lean_ctor_get(v_a_694_, 13);
v___x_768_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_769_ = 0;
v___x_770_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_768_, v___x_721_, v_env_720_, v_declName_690_, v_asyncMode_723_, v___x_769_);
if (lean_obj_tag(v___x_770_) == 1)
{
lean_object* v_val_771_; lean_object* v___y_773_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_val_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_771_);
lean_dec_ref(v___x_770_);
v___x_777_ = l_Lean_Meta_eqnAffectingOptions;
v___x_778_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_778_ == 0)
{
lean_inc_ref(v_options_726_);
v___y_773_ = v_options_726_;
goto v___jp_772_;
}
else
{
uint8_t v___x_779_; 
v___x_779_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_779_ == 0)
{
if (v___x_778_ == 0)
{
lean_inc_ref(v_options_726_);
v___y_773_ = v_options_726_;
goto v___jp_772_;
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_726_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_777_, v___x_780_, v___x_781_, v_options_726_);
v___y_773_ = v___x_782_;
goto v___jp_772_;
}
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_726_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_777_, v___x_783_, v___x_784_, v_options_726_);
v___y_773_ = v___x_785_;
goto v___jp_772_;
}
}
v___jp_772_:
{
size_t v_sz_774_; size_t v___x_775_; lean_object* v___x_776_; 
v_sz_774_ = lean_array_size(v_val_771_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_771_, v_sz_774_, v___x_775_, v___y_773_);
lean_dec(v_val_771_);
v___y_763_ = v___x_776_;
goto v___jp_762_;
}
}
else
{
lean_object* v___x_786_; uint8_t v___x_787_; 
lean_dec(v___x_770_);
v___x_786_ = l_Lean_Meta_eqnAffectingOptions;
v___x_787_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_787_ == 0)
{
lean_inc_ref(v_options_726_);
v___y_763_ = v_options_726_;
goto v___jp_762_;
}
else
{
uint8_t v___x_788_; 
v___x_788_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_788_ == 0)
{
if (v___x_787_ == 0)
{
lean_inc_ref(v_options_726_);
v___y_763_ = v_options_726_;
goto v___jp_762_;
}
else
{
size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((size_t)0ULL);
v___x_790_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_726_);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_786_, v___x_789_, v___x_790_, v_options_726_);
v___y_763_ = v___x_791_;
goto v___jp_762_;
}
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_726_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_786_, v___x_792_, v___x_793_, v_options_726_);
v___y_763_ = v___x_794_;
goto v___jp_762_;
}
}
}
v___jp_697_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_714_ = l_Lean_maxRecDepth;
v___x_715_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_698_, v___x_714_);
lean_inc_ref(v_inheritedTraceOptions_712_);
lean_inc(v_cancelTk_x3f_710_);
lean_inc(v_currMacroScope_709_);
lean_inc(v_quotContext_708_);
lean_inc(v_maxHeartbeats_707_);
lean_inc(v_initHeartbeats_706_);
lean_inc(v_openDecls_705_);
lean_inc(v_currNamespace_704_);
lean_inc(v_ref_703_);
lean_inc(v_currRecDepth_702_);
lean_inc_ref(v_fileMap_701_);
lean_inc_ref(v_fileName_700_);
v___x_716_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_716_, 0, v_fileName_700_);
lean_ctor_set(v___x_716_, 1, v_fileMap_701_);
lean_ctor_set(v___x_716_, 2, v___y_698_);
lean_ctor_set(v___x_716_, 3, v_currRecDepth_702_);
lean_ctor_set(v___x_716_, 4, v___x_715_);
lean_ctor_set(v___x_716_, 5, v_ref_703_);
lean_ctor_set(v___x_716_, 6, v_currNamespace_704_);
lean_ctor_set(v___x_716_, 7, v_openDecls_705_);
lean_ctor_set(v___x_716_, 8, v_initHeartbeats_706_);
lean_ctor_set(v___x_716_, 9, v_maxHeartbeats_707_);
lean_ctor_set(v___x_716_, 10, v_quotContext_708_);
lean_ctor_set(v___x_716_, 11, v_currMacroScope_709_);
lean_ctor_set(v___x_716_, 12, v_cancelTk_x3f_710_);
lean_ctor_set(v___x_716_, 13, v_inheritedTraceOptions_712_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*14, v___y_699_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*14 + 1, v_suppressElabErrors_711_);
lean_inc(v___y_713_);
lean_inc(v_a_693_);
lean_inc_ref(v_a_692_);
v___x_717_ = lean_apply_5(v_act_691_, v_a_692_, v_a_693_, v___x_716_, v___y_713_, lean_box(0));
return v___x_717_;
}
v___jp_738_:
{
if (v___y_741_ == 0)
{
lean_object* v___x_742_; lean_object* v_env_743_; lean_object* v_nextMacroScope_744_; lean_object* v_ngen_745_; lean_object* v_auxDeclNGen_746_; lean_object* v_traceState_747_; lean_object* v_messages_748_; lean_object* v_infoState_749_; lean_object* v_snapshotTasks_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_760_; 
v___x_742_ = lean_st_ref_take(v_a_695_);
v_env_743_ = lean_ctor_get(v___x_742_, 0);
v_nextMacroScope_744_ = lean_ctor_get(v___x_742_, 1);
v_ngen_745_ = lean_ctor_get(v___x_742_, 2);
v_auxDeclNGen_746_ = lean_ctor_get(v___x_742_, 3);
v_traceState_747_ = lean_ctor_get(v___x_742_, 4);
v_messages_748_ = lean_ctor_get(v___x_742_, 6);
v_infoState_749_ = lean_ctor_get(v___x_742_, 7);
v_snapshotTasks_750_ = lean_ctor_get(v___x_742_, 8);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v___x_742_, 5);
lean_dec(v_unused_761_);
v___x_752_ = v___x_742_;
v_isShared_753_ = v_isSharedCheck_760_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snapshotTasks_750_);
lean_inc(v_infoState_749_);
lean_inc(v_messages_748_);
lean_inc(v_traceState_747_);
lean_inc(v_auxDeclNGen_746_);
lean_inc(v_ngen_745_);
lean_inc(v_nextMacroScope_744_);
lean_inc(v_env_743_);
lean_dec(v___x_742_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_760_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = l_Lean_Kernel_enableDiag(v_env_743_, v___y_740_);
v___x_755_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 5, v___x_755_);
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_nextMacroScope_744_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_ngen_745_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_auxDeclNGen_746_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_traceState_747_);
lean_ctor_set(v_reuseFailAlloc_759_, 5, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_759_, 6, v_messages_748_);
lean_ctor_set(v_reuseFailAlloc_759_, 7, v_infoState_749_);
lean_ctor_set(v_reuseFailAlloc_759_, 8, v_snapshotTasks_750_);
v___x_757_ = v_reuseFailAlloc_759_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = lean_st_ref_set(v_a_695_, v___x_757_);
v___y_698_ = v___y_739_;
v___y_699_ = v___y_740_;
v_fileName_700_ = v_fileName_724_;
v_fileMap_701_ = v_fileMap_725_;
v_currRecDepth_702_ = v_currRecDepth_727_;
v_ref_703_ = v_ref_728_;
v_currNamespace_704_ = v_currNamespace_729_;
v_openDecls_705_ = v_openDecls_730_;
v_initHeartbeats_706_ = v_initHeartbeats_731_;
v_maxHeartbeats_707_ = v_maxHeartbeats_732_;
v_quotContext_708_ = v_quotContext_733_;
v_currMacroScope_709_ = v_currMacroScope_734_;
v_cancelTk_x3f_710_ = v_cancelTk_x3f_735_;
v_suppressElabErrors_711_ = v_suppressElabErrors_736_;
v_inheritedTraceOptions_712_ = v_inheritedTraceOptions_737_;
v___y_713_ = v_a_695_;
goto v___jp_697_;
}
}
}
else
{
v___y_698_ = v___y_739_;
v___y_699_ = v___y_740_;
v_fileName_700_ = v_fileName_724_;
v_fileMap_701_ = v_fileMap_725_;
v_currRecDepth_702_ = v_currRecDepth_727_;
v_ref_703_ = v_ref_728_;
v_currNamespace_704_ = v_currNamespace_729_;
v_openDecls_705_ = v_openDecls_730_;
v_initHeartbeats_706_ = v_initHeartbeats_731_;
v_maxHeartbeats_707_ = v_maxHeartbeats_732_;
v_quotContext_708_ = v_quotContext_733_;
v_currMacroScope_709_ = v_currMacroScope_734_;
v_cancelTk_x3f_710_ = v_cancelTk_x3f_735_;
v_suppressElabErrors_711_ = v_suppressElabErrors_736_;
v_inheritedTraceOptions_712_ = v_inheritedTraceOptions_737_;
v___y_713_ = v_a_695_;
goto v___jp_697_;
}
}
v___jp_762_:
{
lean_object* v_env_764_; lean_object* v___x_765_; uint8_t v___x_766_; uint8_t v___x_767_; 
v_env_764_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_env_764_);
lean_dec(v___x_719_);
v___x_765_ = l_Lean_diagnostics;
v___x_766_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_763_, v___x_765_);
v___x_767_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_764_);
lean_dec_ref(v_env_764_);
if (v___x_767_ == 0)
{
if (v___x_766_ == 0)
{
v___y_698_ = v___y_763_;
v___y_699_ = v___x_766_;
v_fileName_700_ = v_fileName_724_;
v_fileMap_701_ = v_fileMap_725_;
v_currRecDepth_702_ = v_currRecDepth_727_;
v_ref_703_ = v_ref_728_;
v_currNamespace_704_ = v_currNamespace_729_;
v_openDecls_705_ = v_openDecls_730_;
v_initHeartbeats_706_ = v_initHeartbeats_731_;
v_maxHeartbeats_707_ = v_maxHeartbeats_732_;
v_quotContext_708_ = v_quotContext_733_;
v_currMacroScope_709_ = v_currMacroScope_734_;
v_cancelTk_x3f_710_ = v_cancelTk_x3f_735_;
v_suppressElabErrors_711_ = v_suppressElabErrors_736_;
v_inheritedTraceOptions_712_ = v_inheritedTraceOptions_737_;
v___y_713_ = v_a_695_;
goto v___jp_697_;
}
else
{
v___y_739_ = v___y_763_;
v___y_740_ = v___x_766_;
v___y_741_ = v___x_767_;
goto v___jp_738_;
}
}
else
{
v___y_739_ = v___y_763_;
v___y_740_ = v___x_766_;
v___y_741_ = v___x_766_;
goto v___jp_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_795_, lean_object* v_act_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_795_, v_act_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_803_, lean_object* v_declName_804_, lean_object* v_act_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_804_, v_act_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_812_, lean_object* v_declName_813_, lean_object* v_act_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_812_, v_declName_813_, v_act_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; lean_object* v_env_825_; lean_object* v_toConstantVal_826_; lean_object* v_value_827_; lean_object* v_all_828_; uint8_t v___y_830_; lean_object* v_type_838_; uint8_t v___x_839_; 
v___x_824_ = lean_st_ref_get(v___y_822_);
v_env_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc_ref_n(v_env_825_, 2);
lean_dec(v___x_824_);
v_toConstantVal_826_ = lean_ctor_get(v_thm_821_, 0);
v_value_827_ = lean_ctor_get(v_thm_821_, 1);
v_all_828_ = lean_ctor_get(v_thm_821_, 2);
v_type_838_ = lean_ctor_get(v_toConstantVal_826_, 2);
v___x_839_ = l_Lean_Environment_hasUnsafe(v_env_825_, v_type_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Environment_hasUnsafe(v_env_825_, v_value_827_);
v___y_830_ = v___x_840_;
goto v___jp_829_;
}
else
{
lean_dec_ref(v_env_825_);
v___y_830_ = v___x_839_;
goto v___jp_829_;
}
v___jp_829_:
{
if (v___y_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_831_, 0, v_thm_821_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_inc(v_all_828_);
lean_inc_ref(v_value_827_);
lean_inc_ref(v_toConstantVal_826_);
lean_dec_ref(v_thm_821_);
v___x_833_ = lean_box(0);
v___x_834_ = 0;
v___x_835_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_835_, 0, v_toConstantVal_826_);
lean_ctor_set(v___x_835_, 1, v_value_827_);
lean_ctor_set(v___x_835_, 2, v___x_833_);
lean_ctor_set(v___x_835_, 3, v_all_828_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*4, v___x_834_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_841_, v___y_842_);
lean_dec(v___y_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_845_, v___y_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_859_, lean_object* v_b_860_, lean_object* v_c_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
v___x_867_ = lean_apply_7(v_k_859_, v_b_860_, v_c_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, lean_box(0));
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_868_, lean_object* v_b_869_, lean_object* v_c_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_868_, v_b_869_, v_c_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_877_, lean_object* v_k_878_, uint8_t v_cleanupAnnotations_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___f_885_; uint8_t v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_885_, 0, v_k_878_);
v___x_886_ = 1;
v___x_887_ = 0;
v___x_888_ = lean_box(0);
v___x_889_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_877_, v___x_886_, v___x_887_, v___x_886_, v___x_887_, v___x_888_, v___f_885_, v_cleanupAnnotations_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_898_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_889_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_889_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_906_, lean_object* v_k_907_, lean_object* v_cleanupAnnotations_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_914_; lean_object* v_res_915_; 
v_cleanupAnnotations_boxed_914_ = lean_unbox(v_cleanupAnnotations_908_);
v_res_915_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_906_, v_k_907_, v_cleanupAnnotations_boxed_914_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_916_, lean_object* v_e_917_, lean_object* v_k_918_, uint8_t v_cleanupAnnotations_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_917_, v_k_918_, v_cleanupAnnotations_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_926_, lean_object* v_e_927_, lean_object* v_k_928_, lean_object* v_cleanupAnnotations_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_935_; lean_object* v_res_936_; 
v_cleanupAnnotations_boxed_935_ = lean_unbox(v_cleanupAnnotations_929_);
v_res_936_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_926_, v_e_927_, v_k_928_, v_cleanupAnnotations_boxed_935_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
if (lean_obj_tag(v_a_937_) == 0)
{
lean_object* v___x_939_; 
v___x_939_ = l_List_reverse___redArg(v_a_938_);
return v___x_939_;
}
else
{
lean_object* v_head_940_; lean_object* v_tail_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_950_; 
v_head_940_ = lean_ctor_get(v_a_937_, 0);
v_tail_941_ = lean_ctor_get(v_a_937_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_937_);
if (v_isSharedCheck_950_ == 0)
{
v___x_943_ = v_a_937_;
v_isShared_944_ = v_isSharedCheck_950_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_tail_941_);
lean_inc(v_head_940_);
lean_dec(v_a_937_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_950_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = l_Lean_mkLevelParam(v_head_940_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v_a_938_);
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_a_938_);
v___x_947_ = v_reuseFailAlloc_949_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
v_a_937_ = v_tail_941_;
v_a_938_ = v___x_947_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_951_, lean_object* v_name_952_, lean_object* v_xs_953_, lean_object* v_body_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_name_960_; lean_object* v_levelParams_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1031_; 
v_name_960_ = lean_ctor_get(v_toConstantVal_951_, 0);
v_levelParams_961_ = lean_ctor_get(v_toConstantVal_951_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_toConstantVal_951_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v_toConstantVal_951_, 2);
lean_dec(v_unused_1032_);
v___x_963_ = v_toConstantVal_951_;
v_isShared_964_ = v_isSharedCheck_1031_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_levelParams_961_);
lean_inc(v_name_960_);
lean_dec(v_toConstantVal_951_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1031_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_lhs_968_; lean_object* v___x_969_; 
v___x_965_ = lean_box(0);
lean_inc(v_levelParams_961_);
v___x_966_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_961_, v___x_965_);
v___x_967_ = l_Lean_mkConst(v_name_960_, v___x_966_);
v_lhs_968_ = l_Lean_mkAppN(v___x_967_, v_xs_953_);
lean_inc_ref(v_lhs_968_);
v___x_969_ = l_Lean_Meta_mkEq(v_lhs_968_, v_body_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; uint8_t v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v___x_969_);
v___x_971_ = 0;
v___x_972_ = 1;
v___x_973_ = 1;
v___x_974_ = l_Lean_Meta_mkForallFVars(v_xs_953_, v_a_970_, v___x_971_, v___x_972_, v___x_972_, v___x_973_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = l_Lean_Meta_letToHave(v_a_975_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref(v___x_976_);
v___x_978_ = l_Lean_Meta_mkEqRefl(v_lhs_968_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref(v___x_978_);
v___x_980_ = l_Lean_Meta_mkLambdaFVars(v_xs_953_, v_a_979_, v___x_971_, v___x_972_, v___x_971_, v___x_972_, v___x_973_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
lean_inc(v_name_952_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 2, v_a_977_);
lean_ctor_set(v___x_963_, 0, v_name_952_);
v___x_983_ = v___x_963_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_name_952_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_levelParams_961_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_a_977_);
v___x_983_ = v_reuseFailAlloc_990_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_a_987_; lean_object* v___x_988_; 
lean_inc(v_name_952_);
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v_name_952_);
lean_ctor_set(v___x_984_, 1, v___x_965_);
v___x_985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v_a_981_);
lean_ctor_set(v___x_985_, 2, v___x_984_);
v___x_986_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_985_, v___y_958_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref(v___x_986_);
v___x_988_ = l_Lean_addDecl(v_a_987_, v___x_971_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v___x_988_);
v___x_989_ = l_Lean_inferDefEqAttr(v_name_952_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_989_;
}
else
{
lean_dec(v_name_952_);
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_a_977_);
lean_del_object(v___x_963_);
lean_dec(v_levelParams_961_);
lean_dec(v_name_952_);
v_a_991_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_980_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_980_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_a_977_);
lean_del_object(v___x_963_);
lean_dec(v_levelParams_961_);
lean_dec(v_name_952_);
v_a_999_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_978_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_978_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_lhs_968_);
lean_del_object(v___x_963_);
lean_dec(v_levelParams_961_);
lean_dec(v_name_952_);
v_a_1007_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_976_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_976_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v_lhs_968_);
lean_del_object(v___x_963_);
lean_dec(v_levelParams_961_);
lean_dec(v_name_952_);
v_a_1015_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_974_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_974_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_lhs_968_);
lean_del_object(v___x_963_);
lean_dec(v_levelParams_961_);
lean_dec(v_name_952_);
v_a_1023_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_969_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_969_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1033_, lean_object* v_name_1034_, lean_object* v_xs_1035_, lean_object* v_body_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1033_, v_name_1034_, v_xs_1035_, v_body_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec_ref(v_xs_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1043_, lean_object* v_info_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_toConstantVal_1050_; lean_object* v_value_1051_; lean_object* v___f_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; 
v_toConstantVal_1050_ = lean_ctor_get(v_info_1044_, 0);
lean_inc_ref(v_toConstantVal_1050_);
v_value_1051_ = lean_ctor_get(v_info_1044_, 1);
lean_inc_ref(v_value_1051_);
lean_dec_ref(v_info_1044_);
v___f_1052_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1052_, 0, v_toConstantVal_1050_);
lean_closure_set(v___f_1052_, 1, v_name_1043_);
v___x_1053_ = 1;
v___x_1054_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1051_, v___f_1052_, v___x_1053_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1055_, lean_object* v_info_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1055_, v_info_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1063_, lean_object* v_name_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___x_1073_; lean_object* v_env_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = lean_st_ref_get(v_a_1068_);
v_env_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_env_1074_);
lean_dec(v___x_1073_);
v___x_1075_ = 0;
lean_inc(v_declName_1063_);
v___x_1076_ = l_Lean_Environment_find_x3f(v_env_1074_, v_declName_1063_, v___x_1075_);
if (lean_obj_tag(v___x_1076_) == 1)
{
lean_object* v_val_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1104_; 
v_val_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1104_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_val_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1104_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
if (lean_obj_tag(v_val_1077_) == 1)
{
lean_object* v_val_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_val_1081_ = lean_ctor_get(v_val_1077_, 0);
lean_inc_ref(v_val_1081_);
lean_dec_ref(v_val_1077_);
lean_inc_n(v_name_1064_, 2);
v___x_1082_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1082_, 0, v_name_1064_);
lean_closure_set(v___x_1082_, 1, v_val_1081_);
lean_inc(v_declName_1063_);
v___x_1083_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1083_, 0, lean_box(0));
lean_closure_set(v___x_1083_, 1, v_declName_1063_);
lean_closure_set(v___x_1083_, 2, v___x_1082_);
v___x_1084_ = l_Lean_Meta_realizeConst(v_declName_1063_, v_name_1064_, v___x_1083_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1094_; 
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v___x_1084_, 0);
lean_dec(v_unused_1095_);
v___x_1086_ = v___x_1084_;
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
else
{
lean_dec(v___x_1084_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_name_1064_);
v___x_1089_ = v___x_1079_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_name_1064_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1089_);
v___x_1091_ = v___x_1086_;
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
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_del_object(v___x_1079_);
lean_dec(v_name_1064_);
v_a_1096_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1084_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1084_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_del_object(v___x_1079_);
lean_dec(v_val_1077_);
lean_dec(v_name_1064_);
lean_dec(v_declName_1063_);
goto v___jp_1070_;
}
}
}
else
{
lean_dec(v___x_1076_);
lean_dec(v_name_1064_);
lean_dec(v_declName_1063_);
goto v___jp_1070_;
}
v___jp_1070_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1105_, lean_object* v_name_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1105_, v_name_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1113_, lean_object* v_vals_1114_, lean_object* v_i_1115_, lean_object* v_k_1116_){
_start:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = lean_array_get_size(v_keys_1113_);
v___x_1118_ = lean_nat_dec_lt(v_i_1115_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec(v_i_1115_);
v___x_1119_ = lean_box(0);
return v___x_1119_;
}
else
{
lean_object* v_k_x27_1120_; uint8_t v___x_1121_; 
v_k_x27_1120_ = lean_array_fget_borrowed(v_keys_1113_, v_i_1115_);
v___x_1121_ = lean_name_eq(v_k_1116_, v_k_x27_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_add(v_i_1115_, v___x_1122_);
lean_dec(v_i_1115_);
v_i_1115_ = v___x_1123_;
goto _start;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_array_fget_borrowed(v_vals_1114_, v_i_1115_);
lean_dec(v_i_1115_);
lean_inc(v___x_1125_);
v___x_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1127_, lean_object* v_vals_1128_, lean_object* v_i_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1127_, v_vals_1128_, v_i_1129_, v_k_1130_);
lean_dec(v_k_1130_);
lean_dec_ref(v_vals_1128_);
lean_dec_ref(v_keys_1127_);
return v_res_1131_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; 
v___x_1132_ = ((size_t)5ULL);
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_shift_left(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; 
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_1137_ = lean_usize_sub(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1138_, size_t v_x_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 0)
{
lean_object* v_es_1141_; lean_object* v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; lean_object* v_j_1146_; lean_object* v___x_1147_; 
v_es_1141_ = lean_ctor_get(v_x_1138_, 0);
v___x_1142_ = lean_box(2);
v___x_1143_ = ((size_t)5ULL);
v___x_1144_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1145_ = lean_usize_land(v_x_1139_, v___x_1144_);
v_j_1146_ = lean_usize_to_nat(v___x_1145_);
v___x_1147_ = lean_array_get_borrowed(v___x_1142_, v_es_1141_, v_j_1146_);
lean_dec(v_j_1146_);
switch(lean_obj_tag(v___x_1147_))
{
case 0:
{
lean_object* v_key_1148_; lean_object* v_val_1149_; uint8_t v___x_1150_; 
v_key_1148_ = lean_ctor_get(v___x_1147_, 0);
v_val_1149_ = lean_ctor_get(v___x_1147_, 1);
v___x_1150_ = lean_name_eq(v_x_1140_, v_key_1148_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_box(0);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; 
lean_inc(v_val_1149_);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_val_1149_);
return v___x_1152_;
}
}
case 1:
{
lean_object* v_node_1153_; size_t v___x_1154_; 
v_node_1153_ = lean_ctor_get(v___x_1147_, 0);
v___x_1154_ = lean_usize_shift_right(v_x_1139_, v___x_1143_);
v_x_1138_ = v_node_1153_;
v_x_1139_ = v___x_1154_;
goto _start;
}
default: 
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_box(0);
return v___x_1156_;
}
}
}
else
{
lean_object* v_ks_1157_; lean_object* v_vs_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_ks_1157_ = lean_ctor_get(v_x_1138_, 0);
v_vs_1158_ = lean_ctor_get(v_x_1138_, 1);
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1157_, v_vs_1158_, v___x_1159_, v_x_1140_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_){
_start:
{
size_t v_x_355__boxed_1164_; lean_object* v_res_1165_; 
v_x_355__boxed_1164_ = lean_unbox_usize(v_x_1162_);
lean_dec(v_x_1162_);
v_res_1165_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1161_, v_x_355__boxed_1164_, v_x_1163_);
lean_dec(v_x_1163_);
lean_dec_ref(v_x_1161_);
return v_res_1165_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1166_; uint64_t v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(1723u);
v___x_1167_ = lean_uint64_of_nat(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
uint64_t v___y_1171_; 
if (lean_obj_tag(v_x_1169_) == 0)
{
uint64_t v___x_1174_; 
v___x_1174_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1171_ = v___x_1174_;
goto v___jp_1170_;
}
else
{
uint64_t v_hash_1175_; 
v_hash_1175_ = lean_ctor_get_uint64(v_x_1169_, sizeof(void*)*2);
v___y_1171_ = v_hash_1175_;
goto v___jp_1170_;
}
v___jp_1170_:
{
size_t v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_uint64_to_usize(v___y_1171_);
v___x_1173_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1168_, v___x_1172_, v_x_1169_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1176_, lean_object* v_x_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1176_, v_x_1177_);
lean_dec(v_x_1177_);
lean_dec_ref(v_x_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_env_1183_; lean_object* v___x_1184_; lean_object* v_asyncMode_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1182_ = lean_st_ref_get(v_a_1180_);
v_env_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_env_1183_);
lean_dec(v___x_1182_);
v___x_1184_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1185_ = lean_ctor_get(v___x_1184_, 2);
v___x_1186_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1187_ = lean_box(0);
v___x_1188_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1186_, v___x_1184_, v_env_1183_, v_asyncMode_1185_, v___x_1187_);
v___x_1189_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1188_, v_thmName_1179_);
lean_dec(v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1191_, v_a_1192_);
lean_dec(v_a_1192_);
lean_dec(v_thmName_1191_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1195_, v_a_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1200_, v_a_1201_, v_a_1202_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_thmName_1200_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1206_, v_x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1209_, v_x_1210_, v_x_1211_);
lean_dec(v_x_1211_);
lean_dec_ref(v_x_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1213_, lean_object* v_x_1214_, size_t v_x_1215_, lean_object* v_x_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1214_, v_x_1215_, v_x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_, lean_object* v_x_1221_){
_start:
{
size_t v_x_460__boxed_1222_; lean_object* v_res_1223_; 
v_x_460__boxed_1222_ = lean_unbox_usize(v_x_1220_);
lean_dec(v_x_1220_);
v_res_1223_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1218_, v_x_1219_, v_x_460__boxed_1222_, v_x_1221_);
lean_dec(v_x_1221_);
lean_dec_ref(v_x_1219_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1224_, lean_object* v_keys_1225_, lean_object* v_vals_1226_, lean_object* v_heq_1227_, lean_object* v_i_1228_, lean_object* v_k_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1225_, v_vals_1226_, v_i_1228_, v_k_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1231_, lean_object* v_keys_1232_, lean_object* v_vals_1233_, lean_object* v_heq_1234_, lean_object* v_i_1235_, lean_object* v_k_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1231_, v_keys_1232_, v_vals_1233_, v_heq_1234_, v_i_1235_, v_k_1236_);
lean_dec(v_k_1236_);
lean_dec_ref(v_vals_1233_);
lean_dec_ref(v_keys_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1238_, lean_object* v_i_1239_, lean_object* v_k_1240_){
_start:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_array_get_size(v_keys_1238_);
v___x_1242_ = lean_nat_dec_lt(v_i_1239_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v_i_1239_);
return v___x_1242_;
}
else
{
lean_object* v_k_x27_1243_; uint8_t v___x_1244_; 
v_k_x27_1243_ = lean_array_fget_borrowed(v_keys_1238_, v_i_1239_);
v___x_1244_ = lean_name_eq(v_k_1240_, v_k_x27_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_add(v_i_1239_, v___x_1245_);
lean_dec(v_i_1239_);
v_i_1239_ = v___x_1246_;
goto _start;
}
else
{
lean_dec(v_i_1239_);
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1248_, lean_object* v_i_1249_, lean_object* v_k_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1248_, v_i_1249_, v_k_1250_);
lean_dec(v_k_1250_);
lean_dec_ref(v_keys_1248_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1253_, size_t v_x_1254_, lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 0)
{
lean_object* v_es_1256_; lean_object* v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v_j_1261_; lean_object* v___x_1262_; 
v_es_1256_ = lean_ctor_get(v_x_1253_, 0);
v___x_1257_ = lean_box(2);
v___x_1258_ = ((size_t)5ULL);
v___x_1259_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1260_ = lean_usize_land(v_x_1254_, v___x_1259_);
v_j_1261_ = lean_usize_to_nat(v___x_1260_);
v___x_1262_ = lean_array_get_borrowed(v___x_1257_, v_es_1256_, v_j_1261_);
lean_dec(v_j_1261_);
switch(lean_obj_tag(v___x_1262_))
{
case 0:
{
lean_object* v_key_1263_; uint8_t v___x_1264_; 
v_key_1263_ = lean_ctor_get(v___x_1262_, 0);
v___x_1264_ = lean_name_eq(v_x_1255_, v_key_1263_);
return v___x_1264_;
}
case 1:
{
lean_object* v_node_1265_; size_t v___x_1266_; 
v_node_1265_ = lean_ctor_get(v___x_1262_, 0);
v___x_1266_ = lean_usize_shift_right(v_x_1254_, v___x_1258_);
v_x_1253_ = v_node_1265_;
v_x_1254_ = v___x_1266_;
goto _start;
}
default: 
{
uint8_t v___x_1268_; 
v___x_1268_ = 0;
return v___x_1268_;
}
}
}
else
{
lean_object* v_ks_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_ks_1269_ = lean_ctor_get(v_x_1253_, 0);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1269_, v___x_1270_, v_x_1255_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
size_t v_x_335__boxed_1275_; uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_x_335__boxed_1275_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_res_1276_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1272_, v_x_335__boxed_1275_, v_x_1274_);
lean_dec(v_x_1274_);
lean_dec_ref(v_x_1272_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
uint64_t v___y_1281_; 
if (lean_obj_tag(v_x_1279_) == 0)
{
uint64_t v___x_1284_; 
v___x_1284_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1281_ = v___x_1284_;
goto v___jp_1280_;
}
else
{
uint64_t v_hash_1285_; 
v_hash_1285_ = lean_ctor_get_uint64(v_x_1279_, sizeof(void*)*2);
v___y_1281_ = v_hash_1285_;
goto v___jp_1280_;
}
v___jp_1280_:
{
size_t v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_uint64_to_usize(v___y_1281_);
v___x_1283_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1278_, v___x_1282_, v_x_1279_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1286_, lean_object* v_x_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1286_, v_x_1287_);
lean_dec(v_x_1287_);
lean_dec_ref(v_x_1286_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v_env_1294_; lean_object* v___x_1295_; lean_object* v_asyncMode_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1293_ = lean_st_ref_get(v_a_1291_);
v_env_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc_ref(v_env_1294_);
lean_dec(v___x_1293_);
v___x_1295_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1296_ = lean_ctor_get(v___x_1295_, 2);
v___x_1297_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1298_ = lean_box(0);
v___x_1299_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1297_, v___x_1295_, v_env_1294_, v_asyncMode_1296_, v___x_1298_);
v___x_1300_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1299_, v_thmName_1290_);
lean_dec(v___x_1299_);
v___x_1301_ = lean_box(v___x_1300_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec(v_thmName_1303_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1307_, v_a_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Meta_isEqnThm(v_thmName_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_thmName_1312_);
return v_res_1316_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1318_, v_x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1321_, v_x_1322_, v_x_1323_);
lean_dec(v_x_1323_);
lean_dec_ref(v_x_1322_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, size_t v_x_1328_, lean_object* v_x_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1327_, v_x_1328_, v_x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
size_t v_x_429__boxed_1335_; uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_x_429__boxed_1335_ = lean_unbox_usize(v_x_1333_);
lean_dec(v_x_1333_);
v_res_1336_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1331_, v_x_1332_, v_x_429__boxed_1335_, v_x_1334_);
lean_dec(v_x_1334_);
lean_dec_ref(v_x_1332_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1338_, lean_object* v_keys_1339_, lean_object* v_vals_1340_, lean_object* v_heq_1341_, lean_object* v_i_1342_, lean_object* v_k_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1339_, v_i_1342_, v_k_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1345_, lean_object* v_keys_1346_, lean_object* v_vals_1347_, lean_object* v_heq_1348_, lean_object* v_i_1349_, lean_object* v_k_1350_){
_start:
{
uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_res_1351_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1345_, v_keys_1346_, v_vals_1347_, v_heq_1348_, v_i_1349_, v_k_1350_);
lean_dec(v_k_1350_);
lean_dec_ref(v_vals_1347_);
lean_dec_ref(v_keys_1346_);
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v_ks_1357_; lean_object* v_vs_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1382_; 
v_ks_1357_ = lean_ctor_get(v_x_1353_, 0);
v_vs_1358_ = lean_ctor_get(v_x_1353_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1353_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1360_ = v_x_1353_;
v_isShared_1361_ = v_isSharedCheck_1382_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_vs_1358_);
lean_inc(v_ks_1357_);
lean_dec(v_x_1353_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1382_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_array_get_size(v_ks_1357_);
v___x_1363_ = lean_nat_dec_lt(v_x_1354_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_dec(v_x_1354_);
v___x_1364_ = lean_array_push(v_ks_1357_, v_x_1355_);
v___x_1365_ = lean_array_push(v_vs_1358_, v_x_1356_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1365_);
lean_ctor_set(v___x_1360_, 0, v___x_1364_);
v___x_1367_ = v___x_1360_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
lean_object* v_k_x27_1369_; uint8_t v___x_1370_; 
v_k_x27_1369_ = lean_array_fget_borrowed(v_ks_1357_, v_x_1354_);
v___x_1370_ = lean_name_eq(v_x_1355_, v_k_x27_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1372_; 
if (v_isShared_1361_ == 0)
{
v___x_1372_ = v___x_1360_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_ks_1357_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_vs_1358_);
v___x_1372_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_add(v_x_1354_, v___x_1373_);
lean_dec(v_x_1354_);
v_x_1353_ = v___x_1372_;
v_x_1354_ = v___x_1374_;
goto _start;
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1377_ = lean_array_fset(v_ks_1357_, v_x_1354_, v_x_1355_);
v___x_1378_ = lean_array_fset(v_vs_1358_, v_x_1354_, v_x_1356_);
lean_dec(v_x_1354_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1378_);
lean_ctor_set(v___x_1360_, 0, v___x_1377_);
v___x_1380_ = v___x_1360_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1378_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1383_, lean_object* v_k_1384_, lean_object* v_v_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1383_, v___x_1386_, v_k_1384_, v_v_1385_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1389_, size_t v_x_1390_, size_t v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_object* v_es_1394_; size_t v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v_j_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_es_1394_ = lean_ctor_get(v_x_1389_, 0);
v___x_1395_ = ((size_t)5ULL);
v___x_1396_ = ((size_t)1ULL);
v___x_1397_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1398_ = lean_usize_land(v_x_1390_, v___x_1397_);
v_j_1399_ = lean_usize_to_nat(v___x_1398_);
v___x_1400_ = lean_array_get_size(v_es_1394_);
v___x_1401_ = lean_nat_dec_lt(v_j_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_dec(v_j_1399_);
lean_dec(v_x_1393_);
lean_dec(v_x_1392_);
return v_x_1389_;
}
else
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1438_; 
lean_inc_ref(v_es_1394_);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1439_);
v___x_1403_ = v_x_1389_;
v_isShared_1404_ = v_isSharedCheck_1438_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v_x_1389_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1438_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v_v_1405_; lean_object* v___x_1406_; lean_object* v_xs_x27_1407_; lean_object* v___y_1409_; 
v_v_1405_ = lean_array_fget(v_es_1394_, v_j_1399_);
v___x_1406_ = lean_box(0);
v_xs_x27_1407_ = lean_array_fset(v_es_1394_, v_j_1399_, v___x_1406_);
switch(lean_obj_tag(v_v_1405_))
{
case 0:
{
lean_object* v_key_1414_; lean_object* v_val_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1425_; 
v_key_1414_ = lean_ctor_get(v_v_1405_, 0);
v_val_1415_ = lean_ctor_get(v_v_1405_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_v_1405_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1417_ = v_v_1405_;
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_val_1415_);
lean_inc(v_key_1414_);
lean_dec(v_v_1405_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_name_eq(v_x_1392_, v_key_1414_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_del_object(v___x_1417_);
v___x_1420_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1414_, v_val_1415_, v_x_1392_, v_x_1393_);
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
v___y_1409_ = v___x_1421_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1423_; 
lean_dec(v_val_1415_);
lean_dec(v_key_1414_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v_x_1393_);
lean_ctor_set(v___x_1417_, 0, v_x_1392_);
v___x_1423_ = v___x_1417_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_x_1392_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_x_1393_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
v___y_1409_ = v___x_1423_;
goto v___jp_1408_;
}
}
}
}
case 1:
{
lean_object* v_node_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1436_; 
v_node_1426_ = lean_ctor_get(v_v_1405_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_v_1405_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1428_ = v_v_1405_;
v_isShared_1429_ = v_isSharedCheck_1436_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_node_1426_);
lean_dec(v_v_1405_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1436_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1430_ = lean_usize_shift_right(v_x_1390_, v___x_1395_);
v___x_1431_ = lean_usize_add(v_x_1391_, v___x_1396_);
v___x_1432_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1426_, v___x_1430_, v___x_1431_, v_x_1392_, v_x_1393_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1432_);
v___x_1434_ = v___x_1428_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
v___y_1409_ = v___x_1434_;
goto v___jp_1408_;
}
}
}
default: 
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_x_1392_);
lean_ctor_set(v___x_1437_, 1, v_x_1393_);
v___y_1409_ = v___x_1437_;
goto v___jp_1408_;
}
}
v___jp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_array_fset(v_xs_x27_1407_, v_j_1399_, v___y_1409_);
lean_dec(v_j_1399_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1410_);
v___x_1412_ = v___x_1403_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
else
{
lean_object* v_ks_1440_; lean_object* v_vs_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1461_; 
v_ks_1440_ = lean_ctor_get(v_x_1389_, 0);
v_vs_1441_ = lean_ctor_get(v_x_1389_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1443_ = v_x_1389_;
v_isShared_1444_ = v_isSharedCheck_1461_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_vs_1441_);
lean_inc(v_ks_1440_);
lean_dec(v_x_1389_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1461_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_ks_1440_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_vs_1441_);
v___x_1446_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v_newNode_1447_; uint8_t v___y_1449_; size_t v___x_1455_; uint8_t v___x_1456_; 
v_newNode_1447_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1446_, v_x_1392_, v_x_1393_);
v___x_1455_ = ((size_t)7ULL);
v___x_1456_ = lean_usize_dec_le(v___x_1455_, v_x_1391_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1457_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1447_);
v___x_1458_ = lean_unsigned_to_nat(4u);
v___x_1459_ = lean_nat_dec_lt(v___x_1457_, v___x_1458_);
lean_dec(v___x_1457_);
v___y_1449_ = v___x_1459_;
goto v___jp_1448_;
}
else
{
v___y_1449_ = v___x_1456_;
goto v___jp_1448_;
}
v___jp_1448_:
{
if (v___y_1449_ == 0)
{
lean_object* v_ks_1450_; lean_object* v_vs_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_ks_1450_ = lean_ctor_get(v_newNode_1447_, 0);
lean_inc_ref(v_ks_1450_);
v_vs_1451_ = lean_ctor_get(v_newNode_1447_, 1);
lean_inc_ref(v_vs_1451_);
lean_dec_ref(v_newNode_1447_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1454_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1391_, v_ks_1450_, v_vs_1451_, v___x_1452_, v___x_1453_);
lean_dec_ref(v_vs_1451_);
lean_dec_ref(v_ks_1450_);
return v___x_1454_;
}
else
{
return v_newNode_1447_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1462_, lean_object* v_keys_1463_, lean_object* v_vals_1464_, lean_object* v_i_1465_, lean_object* v_entries_1466_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = lean_array_get_size(v_keys_1463_);
v___x_1468_ = lean_nat_dec_lt(v_i_1465_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_dec(v_i_1465_);
return v_entries_1466_;
}
else
{
lean_object* v_k_1469_; lean_object* v_v_1470_; uint64_t v___y_1472_; 
v_k_1469_ = lean_array_fget_borrowed(v_keys_1463_, v_i_1465_);
v_v_1470_ = lean_array_fget_borrowed(v_vals_1464_, v_i_1465_);
if (lean_obj_tag(v_k_1469_) == 0)
{
uint64_t v___x_1483_; 
v___x_1483_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1472_ = v___x_1483_;
goto v___jp_1471_;
}
else
{
uint64_t v_hash_1484_; 
v_hash_1484_ = lean_ctor_get_uint64(v_k_1469_, sizeof(void*)*2);
v___y_1472_ = v_hash_1484_;
goto v___jp_1471_;
}
v___jp_1471_:
{
size_t v_h_1473_; size_t v___x_1474_; lean_object* v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v_h_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_h_1473_ = lean_uint64_to_usize(v___y_1472_);
v___x_1474_ = ((size_t)5ULL);
v___x_1475_ = lean_unsigned_to_nat(1u);
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_sub(v_depth_1462_, v___x_1476_);
v___x_1478_ = lean_usize_mul(v___x_1474_, v___x_1477_);
v_h_1479_ = lean_usize_shift_right(v_h_1473_, v___x_1478_);
v___x_1480_ = lean_nat_add(v_i_1465_, v___x_1475_);
lean_dec(v_i_1465_);
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
v___x_1481_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1466_, v_h_1479_, v_depth_1462_, v_k_1469_, v_v_1470_);
v_i_1465_ = v___x_1480_;
v_entries_1466_ = v___x_1481_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1485_, lean_object* v_keys_1486_, lean_object* v_vals_1487_, lean_object* v_i_1488_, lean_object* v_entries_1489_){
_start:
{
size_t v_depth_boxed_1490_; lean_object* v_res_1491_; 
v_depth_boxed_1490_ = lean_unbox_usize(v_depth_1485_);
lean_dec(v_depth_1485_);
v_res_1491_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1490_, v_keys_1486_, v_vals_1487_, v_i_1488_, v_entries_1489_);
lean_dec_ref(v_vals_1487_);
lean_dec_ref(v_keys_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
size_t v_x_634__boxed_1497_; size_t v_x_635__boxed_1498_; lean_object* v_res_1499_; 
v_x_634__boxed_1497_ = lean_unbox_usize(v_x_1493_);
lean_dec(v_x_1493_);
v_x_635__boxed_1498_ = lean_unbox_usize(v_x_1494_);
lean_dec(v_x_1494_);
v_res_1499_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1492_, v_x_634__boxed_1497_, v_x_635__boxed_1498_, v_x_1495_, v_x_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
uint64_t v___y_1504_; 
if (lean_obj_tag(v_x_1501_) == 0)
{
uint64_t v___x_1508_; 
v___x_1508_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1504_ = v___x_1508_;
goto v___jp_1503_;
}
else
{
uint64_t v_hash_1509_; 
v_hash_1509_ = lean_ctor_get_uint64(v_x_1501_, sizeof(void*)*2);
v___y_1504_ = v_hash_1509_;
goto v___jp_1503_;
}
v___jp_1503_:
{
size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_uint64_to_usize(v___y_1504_);
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1500_, v___x_1505_, v___x_1506_, v_x_1501_, v_x_1502_);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1510_, lean_object* v_as_1511_, size_t v_i_1512_, size_t v_stop_1513_, lean_object* v_b_1514_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_eq(v_i_1512_, v_stop_1513_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; 
v___x_1516_ = lean_array_uget_borrowed(v_as_1511_, v_i_1512_);
lean_inc(v_declName_1510_);
lean_inc(v___x_1516_);
v___x_1517_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1514_, v___x_1516_, v_declName_1510_);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1512_, v___x_1518_);
v_i_1512_ = v___x_1519_;
v_b_1514_ = v___x_1517_;
goto _start;
}
else
{
lean_dec(v_declName_1510_);
return v_b_1514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1521_, lean_object* v_as_1522_, lean_object* v_i_1523_, lean_object* v_stop_1524_, lean_object* v_b_1525_){
_start:
{
size_t v_i_boxed_1526_; size_t v_stop_boxed_1527_; lean_object* v_res_1528_; 
v_i_boxed_1526_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_stop_boxed_1527_ = lean_unbox_usize(v_stop_1524_);
lean_dec(v_stop_1524_);
v_res_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1521_, v_as_1522_, v_i_boxed_1526_, v_stop_boxed_1527_, v_b_1525_);
lean_dec_ref(v_as_1522_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1529_, lean_object* v_declName_1530_, lean_object* v_s_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = lean_array_get_size(v_eqThms_1529_);
v___x_1534_ = lean_nat_dec_lt(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_dec(v_declName_1530_);
return v_s_1531_;
}
else
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_nat_dec_le(v___x_1533_, v___x_1533_);
if (v___x_1535_ == 0)
{
if (v___x_1534_ == 0)
{
lean_dec(v_declName_1530_);
return v_s_1531_;
}
else
{
size_t v___x_1536_; size_t v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = ((size_t)0ULL);
v___x_1537_ = lean_usize_of_nat(v___x_1533_);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1530_, v_eqThms_1529_, v___x_1536_, v___x_1537_, v_s_1531_);
return v___x_1538_;
}
}
else
{
size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = ((size_t)0ULL);
v___x_1540_ = lean_usize_of_nat(v___x_1533_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1530_, v_eqThms_1529_, v___x_1539_, v___x_1540_, v_s_1531_);
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1542_, lean_object* v_declName_1543_, lean_object* v_s_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1542_, v_declName_1543_, v_s_1544_);
lean_dec_ref(v_eqThms_1542_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1546_, lean_object* v_eqThms_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v_env_1551_; lean_object* v_nextMacroScope_1552_; lean_object* v_ngen_1553_; lean_object* v_auxDeclNGen_1554_; lean_object* v_traceState_1555_; lean_object* v_messages_1556_; lean_object* v_infoState_1557_; lean_object* v_snapshotTasks_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1574_; 
v___x_1550_ = lean_st_ref_take(v_a_1548_);
v_env_1551_ = lean_ctor_get(v___x_1550_, 0);
v_nextMacroScope_1552_ = lean_ctor_get(v___x_1550_, 1);
v_ngen_1553_ = lean_ctor_get(v___x_1550_, 2);
v_auxDeclNGen_1554_ = lean_ctor_get(v___x_1550_, 3);
v_traceState_1555_ = lean_ctor_get(v___x_1550_, 4);
v_messages_1556_ = lean_ctor_get(v___x_1550_, 6);
v_infoState_1557_ = lean_ctor_get(v___x_1550_, 7);
v_snapshotTasks_1558_ = lean_ctor_get(v___x_1550_, 8);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v___x_1550_, 5);
lean_dec(v_unused_1575_);
v___x_1560_ = v___x_1550_;
v_isShared_1561_ = v_isSharedCheck_1574_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_snapshotTasks_1558_);
lean_inc(v_infoState_1557_);
lean_inc(v_messages_1556_);
lean_inc(v_traceState_1555_);
lean_inc(v_auxDeclNGen_1554_);
lean_inc(v_ngen_1553_);
lean_inc(v_nextMacroScope_1552_);
lean_inc(v_env_1551_);
lean_dec(v___x_1550_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1574_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v_asyncMode_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1562_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1563_ = lean_ctor_get(v___x_1562_, 2);
v___f_1564_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1564_, 0, v_eqThms_1547_);
lean_closure_set(v___f_1564_, 1, v_declName_1546_);
v___x_1565_ = lean_box(0);
v___x_1566_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1562_, v_env_1551_, v___f_1564_, v_asyncMode_1563_, v___x_1565_);
v___x_1567_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 5, v___x_1567_);
lean_ctor_set(v___x_1560_, 0, v___x_1566_);
v___x_1569_ = v___x_1560_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_nextMacroScope_1552_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_ngen_1553_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v_auxDeclNGen_1554_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v_traceState_1555_);
lean_ctor_set(v_reuseFailAlloc_1573_, 5, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1573_, 6, v_messages_1556_);
lean_ctor_set(v_reuseFailAlloc_1573_, 7, v_infoState_1557_);
lean_ctor_set(v_reuseFailAlloc_1573_, 8, v_snapshotTasks_1558_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_st_ref_set(v_a_1548_, v___x_1569_);
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1576_, lean_object* v_eqThms_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1576_, v_eqThms_1577_, v_a_1578_);
lean_dec(v_a_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1581_, lean_object* v_eqThms_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1581_, v_eqThms_1582_, v_a_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1587_, lean_object* v_eqThms_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1587_, v_eqThms_1588_, v_a_1589_, v_a_1590_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1593_, lean_object* v_x_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1594_, v_x_1595_, v_x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1598_, lean_object* v_x_1599_, size_t v_x_1600_, size_t v_x_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1599_, v_x_1600_, v_x_1601_, v_x_1602_, v_x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
size_t v_x_903__boxed_1611_; size_t v_x_904__boxed_1612_; lean_object* v_res_1613_; 
v_x_903__boxed_1611_ = lean_unbox_usize(v_x_1607_);
lean_dec(v_x_1607_);
v_x_904__boxed_1612_ = lean_unbox_usize(v_x_1608_);
lean_dec(v_x_1608_);
v_res_1613_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1605_, v_x_1606_, v_x_903__boxed_1611_, v_x_904__boxed_1612_, v_x_1609_, v_x_1610_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1614_, lean_object* v_n_1615_, lean_object* v_k_1616_, lean_object* v_v_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1615_, v_k_1616_, v_v_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1619_, size_t v_depth_1620_, lean_object* v_keys_1621_, lean_object* v_vals_1622_, lean_object* v_heq_1623_, lean_object* v_i_1624_, lean_object* v_entries_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1620_, v_keys_1621_, v_vals_1622_, v_i_1624_, v_entries_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1627_, lean_object* v_depth_1628_, lean_object* v_keys_1629_, lean_object* v_vals_1630_, lean_object* v_heq_1631_, lean_object* v_i_1632_, lean_object* v_entries_1633_){
_start:
{
size_t v_depth_boxed_1634_; lean_object* v_res_1635_; 
v_depth_boxed_1634_ = lean_unbox_usize(v_depth_1628_);
lean_dec(v_depth_1628_);
v_res_1635_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1627_, v_depth_boxed_1634_, v_keys_1629_, v_vals_1630_, v_heq_1631_, v_i_1632_, v_entries_1633_);
lean_dec_ref(v_vals_1630_);
lean_dec_ref(v_keys_1629_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1637_, v_x_1638_, v_x_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1642_, lean_object* v_env_1643_, lean_object* v_idx_1644_, lean_object* v_eqs_1645_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v_nextEq_1652_; uint8_t v___x_1653_; 
v___x_1647_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_nat_add(v_idx_1644_, v___x_1648_);
lean_dec(v_idx_1644_);
lean_inc(v___x_1649_);
v___x_1650_ = l_Nat_reprFast(v___x_1649_);
v___x_1651_ = lean_string_append(v___x_1647_, v___x_1650_);
lean_dec_ref(v___x_1650_);
lean_inc(v_declName_1642_);
lean_inc_ref(v_env_1643_);
v_nextEq_1652_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1643_, v_declName_1642_, v___x_1651_);
v___x_1653_ = l_Lean_Environment_containsOnBranch(v_env_1643_, v_nextEq_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_dec(v_nextEq_1652_);
lean_dec(v___x_1649_);
lean_dec_ref(v_env_1643_);
lean_dec(v_declName_1642_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_eqs_1645_);
return v___x_1654_;
}
else
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_array_push(v_eqs_1645_, v_nextEq_1652_);
v_idx_1644_ = v___x_1649_;
v_eqs_1645_ = v___x_1655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1657_, lean_object* v_env_1658_, lean_object* v_idx_1659_, lean_object* v_eqs_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1657_, v_env_1658_, v_idx_1659_, v_eqs_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1663_, lean_object* v_env_1664_, lean_object* v_idx_1665_, lean_object* v_eqs_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1663_, v_env_1664_, v_idx_1665_, v_eqs_1666_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1673_, lean_object* v_env_1674_, lean_object* v_idx_1675_, lean_object* v_eqs_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1673_, v_env_1674_, v_idx_1675_, v_eqs_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1686_; lean_object* v_env_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; uint8_t v___x_1691_; 
v___x_1686_ = lean_st_ref_get(v_a_1684_);
v_env_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc_ref_n(v_env_1687_, 3);
lean_dec(v___x_1686_);
v___x_1688_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1683_);
v___x_1689_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1687_, v_declName_1683_, v___x_1688_);
v___x_1690_ = 1;
lean_inc(v___x_1689_);
v___x_1691_ = l_Lean_Environment_contains(v_env_1687_, v___x_1689_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v___x_1689_);
lean_dec_ref(v_env_1687_);
lean_dec(v_declName_1683_);
v___x_1692_ = lean_box(0);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = lean_mk_empty_array_with_capacity(v___x_1694_);
v___x_1696_ = lean_array_push(v___x_1695_, v___x_1689_);
lean_inc(v_declName_1683_);
v___x_1697_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1683_, v_env_1687_, v___x_1694_, v___x_1696_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc_n(v_a_1698_, 2);
lean_dec_ref(v___x_1697_);
v___x_1699_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1683_, v_a_1698_, v_a_1684_);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v___x_1699_, 0);
lean_dec(v_unused_1708_);
v___x_1701_ = v___x_1699_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_dec(v___x_1699_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_a_1698_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_declName_1683_);
v_a_1709_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1697_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1697_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1717_, v_a_1718_);
lean_dec(v_a_1718_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1721_, v_a_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1735_, lean_object* v_localInsts_1736_, lean_object* v_x_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1735_, v_localInsts_1736_, v_x_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1743_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1743_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1760_, lean_object* v_localInsts_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1760_, v_localInsts_1761_, v_x_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1769_, lean_object* v_lctx_1770_, lean_object* v_localInsts_1771_, lean_object* v_x_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1770_, v_localInsts_1771_, v_x_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_lctx_1780_, lean_object* v_localInsts_1781_, lean_object* v_x_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1779_, v_lctx_1780_, v_localInsts_1781_, v_x_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1792_, lean_object* v_as_x27_1793_, lean_object* v_b_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
if (lean_obj_tag(v_as_x27_1793_) == 0)
{
lean_object* v___x_1800_; 
lean_dec(v_declName_1792_);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_b_1794_);
return v___x_1800_;
}
else
{
lean_object* v_head_1801_; lean_object* v_tail_1802_; lean_object* v___x_1803_; 
lean_dec_ref(v_b_1794_);
v_head_1801_ = lean_ctor_get(v_as_x27_1793_, 0);
v_tail_1802_ = lean_ctor_get(v_as_x27_1793_, 1);
lean_inc(v_head_1801_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v_declName_1792_);
v___x_1803_ = lean_apply_6(v_head_1801_, v_declName_1792_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, lean_box(0));
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = lean_box(0);
if (lean_obj_tag(v_a_1804_) == 1)
{
lean_object* v_val_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1816_; 
v_val_1806_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_val_1806_);
v___x_1807_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1792_, v_val_1806_, v___y_1798_);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v___x_1807_, 0);
lean_dec(v_unused_1817_);
v___x_1809_ = v___x_1807_;
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v___x_1807_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1804_);
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v___x_1805_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_a_1804_);
v___x_1818_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1793_ = v_tail_1802_;
v_b_1794_ = v___x_1818_;
goto _start;
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_declName_1792_);
v_a_1820_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1803_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1803_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1828_, lean_object* v_as_x27_1829_, lean_object* v_b_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1828_, v_as_x27_1829_, v_b_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v_as_x27_1829_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
lean_inc(v_declName_1837_);
v___x_1843_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1881_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1881_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1881_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_unbox(v_a_1844_);
lean_dec(v_a_1844_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec(v_declName_1837_);
v___x_1849_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1849_);
v___x_1851_ = v___x_1846_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
lean_object* v___x_1853_; 
lean_del_object(v___x_1846_);
lean_inc(v_declName_1837_);
v___x_1853_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1837_, v___y_1841_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
if (lean_obj_tag(v_a_1854_) == 1)
{
lean_dec_ref(v_a_1854_);
lean_dec(v_declName_1837_);
return v___x_1853_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v___x_1853_);
lean_dec(v_a_1854_);
v___x_1855_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1856_ = lean_st_ref_get(v___x_1855_);
v___x_1857_ = lean_box(0);
v___x_1858_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1859_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1837_, v___x_1856_, v___x_1858_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___x_1856_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1872_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1872_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1872_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_fst_1864_; 
v_fst_1864_ = lean_ctor_get(v_a_1860_, 0);
lean_inc(v_fst_1864_);
lean_dec(v_a_1860_);
if (lean_obj_tag(v_fst_1864_) == 0)
{
lean_object* v___x_1866_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1857_);
v___x_1866_ = v___x_1862_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1857_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
else
{
lean_object* v_val_1868_; lean_object* v___x_1870_; 
v_val_1868_ = lean_ctor_get(v_fst_1864_, 0);
lean_inc(v_val_1868_);
lean_dec_ref(v_fst_1864_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v_val_1868_);
v___x_1870_ = v___x_1862_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_val_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1859_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1859_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
else
{
lean_dec(v_declName_1837_);
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_declName_1837_);
v_a_1882_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1843_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1843_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = lean_box(1);
v___x_1901_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1902_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___x_1901_);
lean_ctor_set(v___x_1903_, 2, v___x_1900_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___f_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___f_1912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1912_, 0, v_declName_1906_);
v___x_1913_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1914_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1915_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1913_, v___x_1914_, v___f_1912_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1923_, lean_object* v_as_1924_, lean_object* v_as_x27_1925_, lean_object* v_b_1926_, lean_object* v_a_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1923_, v_as_x27_1925_, v_b_1926_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1934_, lean_object* v_as_1935_, lean_object* v_as_x27_1936_, lean_object* v_b_1937_, lean_object* v_a_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1934_, v_as_1935_, v_as_x27_1936_, v_b_1937_, v_a_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v_as_x27_1936_);
lean_dec(v_as_1935_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1951_ = lean_unsigned_to_nat(32u);
v___x_1952_ = lean_mk_empty_array_with_capacity(v___x_1951_);
lean_dec_ref(v___x_1952_);
v___x_1953_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1954_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1945_);
v___x_1955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1955_, 0, v_declName_1945_);
v___x_1956_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1956_, 0, lean_box(0));
lean_closure_set(v___x_1956_, 1, v_declName_1945_);
lean_closure_set(v___x_1956_, 2, v___x_1955_);
v___x_1957_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1953_, v___x_1954_, v___x_1956_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; lean_object* v_env_1972_; lean_object* v___x_1973_; lean_object* v_mctx_1974_; lean_object* v_lctx_1975_; lean_object* v_options_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1971_ = lean_st_ref_get(v___y_1969_);
v_env_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc_ref(v_env_1972_);
lean_dec(v___x_1971_);
v___x_1973_ = lean_st_ref_get(v___y_1967_);
v_mctx_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc_ref(v_mctx_1974_);
lean_dec(v___x_1973_);
v_lctx_1975_ = lean_ctor_get(v___y_1966_, 2);
v_options_1976_ = lean_ctor_get(v___y_1968_, 2);
lean_inc_ref(v_options_1976_);
lean_inc_ref(v_lctx_1975_);
v___x_1977_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1977_, 0, v_env_1972_);
lean_ctor_set(v___x_1977_, 1, v_mctx_1974_);
lean_ctor_set(v___x_1977_, 2, v_lctx_1975_);
lean_ctor_set(v___x_1977_, 3, v_options_1976_);
v___x_1978_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v_msgData_1965_);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1986_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1987_; double v___x_1988_; 
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_float_of_nat(v___x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1992_, lean_object* v_msg_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_ref_1999_; lean_object* v___x_2000_; lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2045_; 
v_ref_1999_ = lean_ctor_get(v___y_1996_, 5);
v___x_2000_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2045_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2045_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v_traceState_2006_; lean_object* v_env_2007_; lean_object* v_nextMacroScope_2008_; lean_object* v_ngen_2009_; lean_object* v_auxDeclNGen_2010_; lean_object* v_cache_2011_; lean_object* v_messages_2012_; lean_object* v_infoState_2013_; lean_object* v_snapshotTasks_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2044_; 
v___x_2005_ = lean_st_ref_take(v___y_1997_);
v_traceState_2006_ = lean_ctor_get(v___x_2005_, 4);
v_env_2007_ = lean_ctor_get(v___x_2005_, 0);
v_nextMacroScope_2008_ = lean_ctor_get(v___x_2005_, 1);
v_ngen_2009_ = lean_ctor_get(v___x_2005_, 2);
v_auxDeclNGen_2010_ = lean_ctor_get(v___x_2005_, 3);
v_cache_2011_ = lean_ctor_get(v___x_2005_, 5);
v_messages_2012_ = lean_ctor_get(v___x_2005_, 6);
v_infoState_2013_ = lean_ctor_get(v___x_2005_, 7);
v_snapshotTasks_2014_ = lean_ctor_get(v___x_2005_, 8);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2016_ = v___x_2005_;
v_isShared_2017_ = v_isSharedCheck_2044_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_snapshotTasks_2014_);
lean_inc(v_infoState_2013_);
lean_inc(v_messages_2012_);
lean_inc(v_cache_2011_);
lean_inc(v_traceState_2006_);
lean_inc(v_auxDeclNGen_2010_);
lean_inc(v_ngen_2009_);
lean_inc(v_nextMacroScope_2008_);
lean_inc(v_env_2007_);
lean_dec(v___x_2005_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2044_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
uint64_t v_tid_2018_; lean_object* v_traces_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2043_; 
v_tid_2018_ = lean_ctor_get_uint64(v_traceState_2006_, sizeof(void*)*1);
v_traces_2019_ = lean_ctor_get(v_traceState_2006_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_traceState_2006_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2021_ = v_traceState_2006_;
v_isShared_2022_ = v_isSharedCheck_2043_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_traces_2019_);
lean_dec(v_traceState_2006_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2043_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; double v___x_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2023_ = lean_box(0);
v___x_2024_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_2025_ = 0;
v___x_2026_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_2027_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2027_, 0, v_cls_1992_);
lean_ctor_set(v___x_2027_, 1, v___x_2023_);
lean_ctor_set(v___x_2027_, 2, v___x_2026_);
lean_ctor_set_float(v___x_2027_, sizeof(void*)*3, v___x_2024_);
lean_ctor_set_float(v___x_2027_, sizeof(void*)*3 + 8, v___x_2024_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*3 + 16, v___x_2025_);
v___x_2028_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_2029_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v_a_2001_);
lean_ctor_set(v___x_2029_, 2, v___x_2028_);
lean_inc(v_ref_1999_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_ref_1999_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = l_Lean_PersistentArray_push___redArg(v_traces_2019_, v___x_2030_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2031_);
v___x_2033_ = v___x_2021_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2031_);
lean_ctor_set_uint64(v_reuseFailAlloc_2042_, sizeof(void*)*1, v_tid_2018_);
v___x_2033_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2035_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 4, v___x_2033_);
v___x_2035_ = v___x_2016_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_env_2007_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_nextMacroScope_2008_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_ngen_2009_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_auxDeclNGen_2010_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2041_, 5, v_cache_2011_);
lean_ctor_set(v_reuseFailAlloc_2041_, 6, v_messages_2012_);
lean_ctor_set(v_reuseFailAlloc_2041_, 7, v_infoState_2013_);
lean_ctor_set(v_reuseFailAlloc_2041_, 8, v_snapshotTasks_2014_);
v___x_2035_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2036_ = lean_st_ref_set(v___y_1997_, v___x_2035_);
v___x_2037_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2037_);
v___x_2039_ = v___x_2003_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2046_, lean_object* v_msg_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2046_, v_msg_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2054_, lean_object* v_as_2055_, size_t v_sz_2056_, size_t v_i_2057_, lean_object* v_b_2058_){
_start:
{
lean_object* v_a_2061_; uint8_t v___x_2065_; 
v___x_2065_ = lean_usize_dec_lt(v_i_2057_, v_sz_2056_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_b_2058_);
return v___x_2066_;
}
else
{
lean_object* v_a_2067_; lean_object* v_defValue_2068_; uint8_t v___x_2069_; uint8_t v___y_2071_; 
v_a_2067_ = lean_array_uget(v_as_2055_, v_i_2057_);
v_defValue_2068_ = lean_ctor_get(v_a_2067_, 1);
v___x_2069_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2054_, v_a_2067_);
if (v___x_2069_ == 0)
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_unbox(v_defValue_2068_);
if (v___x_2083_ == 0)
{
v___y_2071_ = v___x_2065_;
goto v___jp_2070_;
}
else
{
v___y_2071_ = v___x_2069_;
goto v___jp_2070_;
}
}
else
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_unbox(v_defValue_2068_);
v___y_2071_ = v___x_2084_;
goto v___jp_2070_;
}
v___jp_2070_:
{
if (v___y_2071_ == 0)
{
lean_object* v_name_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2081_; 
v_name_2072_ = lean_ctor_get(v_a_2067_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v_a_2067_, 1);
lean_dec(v_unused_2082_);
v___x_2074_ = v_a_2067_;
v_isShared_2075_ = v_isSharedCheck_2081_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_name_2072_);
lean_dec(v_a_2067_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2081_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2076_, 0, v___x_2069_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_name_2072_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_array_push(v_b_2058_, v___x_2078_);
v_a_2061_ = v___x_2079_;
goto v___jp_2060_;
}
}
}
else
{
lean_dec(v_a_2067_);
v_a_2061_ = v_b_2058_;
goto v___jp_2060_;
}
}
}
v___jp_2060_:
{
size_t v___x_2062_; size_t v___x_2063_; 
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = lean_usize_add(v_i_2057_, v___x_2062_);
v_i_2057_ = v___x_2063_;
v_b_2058_ = v_a_2061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2085_, lean_object* v_as_2086_, lean_object* v_sz_2087_, lean_object* v_i_2088_, lean_object* v_b_2089_, lean_object* v___y_2090_){
_start:
{
size_t v_sz_boxed_2091_; size_t v_i_boxed_2092_; lean_object* v_res_2093_; 
v_sz_boxed_2091_ = lean_unbox_usize(v_sz_2087_);
lean_dec(v_sz_2087_);
v_i_boxed_2092_ = lean_unbox_usize(v_i_2088_);
lean_dec(v_i_2088_);
v_res_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2085_, v_as_2086_, v_sz_boxed_2091_, v_i_boxed_2092_, v_b_2089_);
lean_dec_ref(v_as_2086_);
lean_dec_ref(v___x_2085_);
return v_res_2093_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2096_; size_t v_sz_2097_; 
v___x_2096_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2097_ = lean_array_size(v___x_2096_);
return v_sz_2097_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2099_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
lean_ctor_set(v___x_2099_, 2, v___x_2098_);
lean_ctor_set(v___x_2099_, 3, v___x_2098_);
lean_ctor_set(v___x_2099_, 4, v___x_2098_);
lean_ctor_set(v___x_2099_, 5, v___x_2098_);
return v___x_2099_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2108_ = l_Lean_Name_append(v___x_2107_, v___x_2106_);
return v___x_2108_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2111_ = l_Lean_stringToMessageData(v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_options_2118_; lean_object* v_inheritedTraceOptions_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; size_t v_sz_2123_; size_t v___x_2124_; lean_object* v___x_2125_; 
v_options_2118_ = lean_ctor_get(v_a_2115_, 2);
v_inheritedTraceOptions_2119_ = lean_ctor_get(v_a_2115_, 13);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2122_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2123_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2124_ = ((size_t)0ULL);
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2118_, v___x_2122_, v_sz_2123_, v___x_2124_, v___x_2121_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2185_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2185_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2185_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = lean_array_get_size(v_a_2126_);
v___x_2174_ = lean_nat_dec_eq(v___x_2173_, v___x_2120_);
if (v___x_2174_ == 0)
{
uint8_t v_hasTrace_2175_; 
v_hasTrace_2175_ = lean_ctor_get_uint8(v_options_2118_, sizeof(void*)*1);
if (v_hasTrace_2175_ == 0)
{
v___y_2131_ = v_a_2114_;
v___y_2132_ = v_a_2116_;
goto v___jp_2130_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2176_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2177_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2119_, v_options_2118_, v___x_2177_);
if (v___x_2178_ == 0)
{
v___y_2131_ = v_a_2114_;
v___y_2132_ = v_a_2116_;
goto v___jp_2130_;
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2179_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2112_);
v___x_2180_ = l_Lean_MessageData_ofName(v_declName_2112_);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2176_, v___x_2181_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_dec_ref(v___x_2182_);
v___y_2131_ = v_a_2114_;
v___y_2132_ = v_a_2116_;
goto v___jp_2130_;
}
else
{
lean_del_object(v___x_2128_);
lean_dec(v_a_2126_);
lean_dec(v_declName_2112_);
return v___x_2182_;
}
}
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_del_object(v___x_2128_);
lean_dec(v_a_2126_);
lean_dec(v_declName_2112_);
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
return v___x_2184_;
}
v___jp_2130_:
{
lean_object* v___x_2133_; lean_object* v_env_2134_; lean_object* v_nextMacroScope_2135_; lean_object* v_ngen_2136_; lean_object* v_auxDeclNGen_2137_; lean_object* v_traceState_2138_; lean_object* v_messages_2139_; lean_object* v_infoState_2140_; lean_object* v_snapshotTasks_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2171_; 
v___x_2133_ = lean_st_ref_take(v___y_2132_);
v_env_2134_ = lean_ctor_get(v___x_2133_, 0);
v_nextMacroScope_2135_ = lean_ctor_get(v___x_2133_, 1);
v_ngen_2136_ = lean_ctor_get(v___x_2133_, 2);
v_auxDeclNGen_2137_ = lean_ctor_get(v___x_2133_, 3);
v_traceState_2138_ = lean_ctor_get(v___x_2133_, 4);
v_messages_2139_ = lean_ctor_get(v___x_2133_, 6);
v_infoState_2140_ = lean_ctor_get(v___x_2133_, 7);
v_snapshotTasks_2141_ = lean_ctor_get(v___x_2133_, 8);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; 
v_unused_2172_ = lean_ctor_get(v___x_2133_, 5);
lean_dec(v_unused_2172_);
v___x_2143_ = v___x_2133_;
v_isShared_2144_ = v_isSharedCheck_2171_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_snapshotTasks_2141_);
lean_inc(v_infoState_2140_);
lean_inc(v_messages_2139_);
lean_inc(v_traceState_2138_);
lean_inc(v_auxDeclNGen_2137_);
lean_inc(v_ngen_2136_);
lean_inc(v_nextMacroScope_2135_);
lean_inc(v_env_2134_);
lean_dec(v___x_2133_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2171_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2145_ = l_Lean_Meta_eqnOptionsExt;
v___x_2146_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2145_, v_env_2134_, v_declName_2112_, v_a_2126_);
v___x_2147_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 5, v___x_2147_);
lean_ctor_set(v___x_2143_, 0, v___x_2146_);
v___x_2149_ = v___x_2143_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_nextMacroScope_2135_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_ngen_2136_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_auxDeclNGen_2137_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v_traceState_2138_);
lean_ctor_set(v_reuseFailAlloc_2170_, 5, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2170_, 6, v_messages_2139_);
lean_ctor_set(v_reuseFailAlloc_2170_, 7, v_infoState_2140_);
lean_ctor_set(v_reuseFailAlloc_2170_, 8, v_snapshotTasks_2141_);
v___x_2149_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_mctx_2152_; lean_object* v_zetaDeltaFVarIds_2153_; lean_object* v_postponed_2154_; lean_object* v_diag_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2168_; 
v___x_2150_ = lean_st_ref_set(v___y_2132_, v___x_2149_);
v___x_2151_ = lean_st_ref_take(v___y_2131_);
v_mctx_2152_ = lean_ctor_get(v___x_2151_, 0);
v_zetaDeltaFVarIds_2153_ = lean_ctor_get(v___x_2151_, 2);
v_postponed_2154_ = lean_ctor_get(v___x_2151_, 3);
v_diag_2155_ = lean_ctor_get(v___x_2151_, 4);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2151_, 1);
lean_dec(v_unused_2169_);
v___x_2157_ = v___x_2151_;
v_isShared_2158_ = v_isSharedCheck_2168_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_diag_2155_);
lean_inc(v_postponed_2154_);
lean_inc(v_zetaDeltaFVarIds_2153_);
lean_inc(v_mctx_2152_);
lean_dec(v___x_2151_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2168_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v___x_2159_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_mctx_2152_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_zetaDeltaFVarIds_2153_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_postponed_2154_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_diag_2155_);
v___x_2161_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2162_ = lean_st_ref_set(v___y_2131_, v___x_2161_);
v___x_2163_ = lean_box(0);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2163_);
v___x_2165_ = v___x_2128_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
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
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_declName_2112_);
v_a_2186_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2125_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2125_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2201_, lean_object* v_as_2202_, size_t v_sz_2203_, size_t v_i_2204_, lean_object* v_b_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2201_, v_as_2202_, v_sz_2203_, v_i_2204_, v_b_2205_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2212_, lean_object* v_as_2213_, lean_object* v_sz_2214_, lean_object* v_i_2215_, lean_object* v_b_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
size_t v_sz_boxed_2222_; size_t v_i_boxed_2223_; lean_object* v_res_2224_; 
v_sz_boxed_2222_ = lean_unbox_usize(v_sz_2214_);
lean_dec(v_sz_2214_);
v_i_boxed_2223_ = lean_unbox_usize(v_i_2215_);
lean_dec(v_i_2215_);
v_res_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2212_, v_as_2213_, v_sz_boxed_2222_, v_i_boxed_2223_, v_b_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v_as_2213_);
lean_dec_ref(v___x_2212_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = lean_box(0);
v___x_2227_ = lean_st_mk_ref(v___x_2226_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2250_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2250_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2250_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_unbox(v_a_2234_);
lean_dec(v_a_2234_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec_ref(v_f_2231_);
v___x_2239_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 1);
lean_ctor_set(v___x_2236_, 0, v___x_2239_);
v___x_2241_ = v___x_2236_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2243_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2244_ = lean_st_ref_take(v___x_2243_);
v___x_2245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2245_, 0, v_f_2231_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = lean_st_ref_set(v___x_2243_, v___x_2245_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2246_);
v___x_2248_ = v___x_2236_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref(v_f_2231_);
v_a_2251_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2233_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2233_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2259_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2265_, lean_object* v_as_x27_2266_, lean_object* v_b_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
if (lean_obj_tag(v_as_x27_2266_) == 0)
{
lean_object* v___x_2273_; 
lean_dec(v_declName_2265_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_b_2267_);
return v___x_2273_;
}
else
{
lean_object* v_head_2274_; lean_object* v_tail_2275_; lean_object* v___x_2276_; 
lean_dec_ref(v_b_2267_);
v_head_2274_ = lean_ctor_get(v_as_x27_2266_, 0);
v_tail_2275_ = lean_ctor_get(v_as_x27_2266_, 1);
lean_inc(v_head_2274_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
lean_inc(v_declName_2265_);
v___x_2276_ = lean_apply_6(v_head_2274_, v_declName_2265_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, lean_box(0));
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2289_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2289_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2289_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_box(0);
if (lean_obj_tag(v_a_2277_) == 1)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
lean_dec(v_declName_2265_);
v___x_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_a_2277_);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v___x_2281_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2283_);
v___x_2285_ = v___x_2279_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
else
{
lean_object* v___x_2287_; 
lean_del_object(v___x_2279_);
lean_dec(v_a_2277_);
v___x_2287_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2266_ = v_tail_2275_;
v_b_2267_ = v___x_2287_;
goto _start;
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_declName_2265_);
v_a_2290_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2276_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2276_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2298_, lean_object* v_as_x27_2299_, lean_object* v_b_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2298_, v_as_x27_2299_, v_b_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v_as_x27_2299_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2307_, lean_object* v_declName_2308_, uint8_t v_nonRec_2309_, lean_object* v___x_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2319_; lean_object* v_env_2320_; uint8_t v___x_2321_; uint8_t v___x_2322_; 
v___x_2319_ = lean_st_ref_get(v___y_2314_);
v_env_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc_ref(v_env_2320_);
lean_dec(v___x_2319_);
v___x_2321_ = 1;
lean_inc(v___x_2307_);
v___x_2322_ = l_Lean_Environment_contains(v_env_2320_, v___x_2307_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
lean_dec(v___x_2307_);
lean_inc(v_declName_2308_);
v___x_2323_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2308_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; uint8_t v___x_2325_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = lean_unbox(v_a_2324_);
lean_dec(v_a_2324_);
if (v___x_2325_ == 0)
{
lean_dec_ref(v___x_2310_);
lean_dec(v_declName_2308_);
goto v___jp_2316_;
}
else
{
lean_object* v___x_2326_; 
lean_inc(v_declName_2308_);
v___x_2326_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2308_, v___y_2314_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; uint8_t v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2326_);
v___x_2328_ = lean_unbox(v_a_2327_);
lean_dec(v_a_2327_);
if (v___x_2328_ == 0)
{
if (v_nonRec_2309_ == 0)
{
lean_dec_ref(v___x_2310_);
lean_dec(v_declName_2308_);
goto v___jp_2316_;
}
else
{
lean_object* v___x_2329_; lean_object* v_env_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_st_ref_get(v___y_2314_);
v_env_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc_ref(v_env_2330_);
lean_dec(v___x_2329_);
lean_inc(v_declName_2308_);
v___x_2331_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2330_, v_declName_2308_, v___x_2310_);
v___x_2332_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2308_, v___x_2331_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
return v___x_2332_;
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec_ref(v___x_2310_);
v___x_2333_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2334_ = lean_st_ref_get(v___x_2333_);
v___x_2335_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2336_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2308_, v___x_2334_, v___x_2335_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___x_2334_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2346_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2346_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2346_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_fst_2341_; 
v_fst_2341_ = lean_ctor_get(v_a_2337_, 0);
lean_inc(v_fst_2341_);
lean_dec(v_a_2337_);
if (lean_obj_tag(v_fst_2341_) == 0)
{
lean_del_object(v___x_2339_);
goto v___jp_2316_;
}
else
{
lean_object* v_val_2342_; lean_object* v___x_2344_; 
v_val_2342_ = lean_ctor_get(v_fst_2341_, 0);
lean_inc(v_val_2342_);
lean_dec_ref(v_fst_2341_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v_val_2342_);
v___x_2344_ = v___x_2339_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_val_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
v_a_2347_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2336_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2336_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v___x_2310_);
lean_dec(v_declName_2308_);
v_a_2355_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2326_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2326_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___x_2310_);
lean_dec(v_declName_2308_);
v_a_2363_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2323_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2323_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec_ref(v___x_2310_);
lean_dec(v_declName_2308_);
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2307_);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
v___jp_2316_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2373_, lean_object* v_declName_2374_, lean_object* v_nonRec_2375_, lean_object* v___x_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v_nonRec_boxed_2382_; lean_object* v_res_2383_; 
v_nonRec_boxed_2382_ = lean_unbox(v_nonRec_2375_);
v_res_2383_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2373_, v_declName_2374_, v_nonRec_boxed_2382_, v___x_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_ref_2390_; lean_object* v___x_2391_; lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2400_; 
v_ref_2390_ = lean_ctor_get(v___y_2387_, 5);
v___x_2391_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
lean_inc(v_ref_2390_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v_ref_2390_);
lean_ctor_set(v___x_2396_, 1, v_a_2392_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set_tag(v___x_2394_, 1);
lean_ctor_set(v___x_2394_, 0, v___x_2396_);
v___x_2398_ = v___x_2394_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2408_, uint8_t v_isExporting_2409_, lean_object* v___x_2410_, lean_object* v___y_2411_, lean_object* v___x_2412_, lean_object* v_a_x3f_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_env_2416_; lean_object* v_nextMacroScope_2417_; lean_object* v_ngen_2418_; lean_object* v_auxDeclNGen_2419_; lean_object* v_traceState_2420_; lean_object* v_messages_2421_; lean_object* v_infoState_2422_; lean_object* v_snapshotTasks_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2448_; 
v___x_2415_ = lean_st_ref_take(v___y_2408_);
v_env_2416_ = lean_ctor_get(v___x_2415_, 0);
v_nextMacroScope_2417_ = lean_ctor_get(v___x_2415_, 1);
v_ngen_2418_ = lean_ctor_get(v___x_2415_, 2);
v_auxDeclNGen_2419_ = lean_ctor_get(v___x_2415_, 3);
v_traceState_2420_ = lean_ctor_get(v___x_2415_, 4);
v_messages_2421_ = lean_ctor_get(v___x_2415_, 6);
v_infoState_2422_ = lean_ctor_get(v___x_2415_, 7);
v_snapshotTasks_2423_ = lean_ctor_get(v___x_2415_, 8);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; 
v_unused_2449_ = lean_ctor_get(v___x_2415_, 5);
lean_dec(v_unused_2449_);
v___x_2425_ = v___x_2415_;
v_isShared_2426_ = v_isSharedCheck_2448_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_snapshotTasks_2423_);
lean_inc(v_infoState_2422_);
lean_inc(v_messages_2421_);
lean_inc(v_traceState_2420_);
lean_inc(v_auxDeclNGen_2419_);
lean_inc(v_ngen_2418_);
lean_inc(v_nextMacroScope_2417_);
lean_inc(v_env_2416_);
lean_dec(v___x_2415_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2448_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = l_Lean_Environment_setExporting(v_env_2416_, v_isExporting_2409_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 5, v___x_2410_);
lean_ctor_set(v___x_2425_, 0, v___x_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_nextMacroScope_2417_);
lean_ctor_set(v_reuseFailAlloc_2447_, 2, v_ngen_2418_);
lean_ctor_set(v_reuseFailAlloc_2447_, 3, v_auxDeclNGen_2419_);
lean_ctor_set(v_reuseFailAlloc_2447_, 4, v_traceState_2420_);
lean_ctor_set(v_reuseFailAlloc_2447_, 5, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2447_, 6, v_messages_2421_);
lean_ctor_set(v_reuseFailAlloc_2447_, 7, v_infoState_2422_);
lean_ctor_set(v_reuseFailAlloc_2447_, 8, v_snapshotTasks_2423_);
v___x_2429_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_mctx_2432_; lean_object* v_zetaDeltaFVarIds_2433_; lean_object* v_postponed_2434_; lean_object* v_diag_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2445_; 
v___x_2430_ = lean_st_ref_set(v___y_2408_, v___x_2429_);
v___x_2431_ = lean_st_ref_take(v___y_2411_);
v_mctx_2432_ = lean_ctor_get(v___x_2431_, 0);
v_zetaDeltaFVarIds_2433_ = lean_ctor_get(v___x_2431_, 2);
v_postponed_2434_ = lean_ctor_get(v___x_2431_, 3);
v_diag_2435_ = lean_ctor_get(v___x_2431_, 4);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; 
v_unused_2446_ = lean_ctor_get(v___x_2431_, 1);
lean_dec(v_unused_2446_);
v___x_2437_ = v___x_2431_;
v_isShared_2438_ = v_isSharedCheck_2445_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_diag_2435_);
lean_inc(v_postponed_2434_);
lean_inc(v_zetaDeltaFVarIds_2433_);
lean_inc(v_mctx_2432_);
lean_dec(v___x_2431_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2445_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 1, v___x_2412_);
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_mctx_2432_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_zetaDeltaFVarIds_2433_);
lean_ctor_set(v_reuseFailAlloc_2444_, 3, v_postponed_2434_);
lean_ctor_set(v_reuseFailAlloc_2444_, 4, v_diag_2435_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_st_ref_set(v___y_2411_, v___x_2440_);
v___x_2442_ = lean_box(0);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2450_, lean_object* v_isExporting_2451_, lean_object* v___x_2452_, lean_object* v___y_2453_, lean_object* v___x_2454_, lean_object* v_a_x3f_2455_, lean_object* v___y_2456_){
_start:
{
uint8_t v_isExporting_boxed_2457_; lean_object* v_res_2458_; 
v_isExporting_boxed_2457_ = lean_unbox(v_isExporting_2451_);
v_res_2458_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2450_, v_isExporting_boxed_2457_, v___x_2452_, v___y_2453_, v___x_2454_, v_a_x3f_2455_);
lean_dec(v_a_x3f_2455_);
lean_dec(v___y_2453_);
lean_dec(v___y_2450_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2459_, uint8_t v_isExporting_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; lean_object* v_env_2467_; uint8_t v_isExporting_2468_; lean_object* v___x_2469_; lean_object* v_env_2470_; lean_object* v_nextMacroScope_2471_; lean_object* v_ngen_2472_; lean_object* v_auxDeclNGen_2473_; lean_object* v_traceState_2474_; lean_object* v_messages_2475_; lean_object* v_infoState_2476_; lean_object* v_snapshotTasks_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2531_; 
v___x_2466_ = lean_st_ref_get(v___y_2464_);
v_env_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc_ref(v_env_2467_);
lean_dec(v___x_2466_);
v_isExporting_2468_ = lean_ctor_get_uint8(v_env_2467_, sizeof(void*)*8);
lean_dec_ref(v_env_2467_);
v___x_2469_ = lean_st_ref_take(v___y_2464_);
v_env_2470_ = lean_ctor_get(v___x_2469_, 0);
v_nextMacroScope_2471_ = lean_ctor_get(v___x_2469_, 1);
v_ngen_2472_ = lean_ctor_get(v___x_2469_, 2);
v_auxDeclNGen_2473_ = lean_ctor_get(v___x_2469_, 3);
v_traceState_2474_ = lean_ctor_get(v___x_2469_, 4);
v_messages_2475_ = lean_ctor_get(v___x_2469_, 6);
v_infoState_2476_ = lean_ctor_get(v___x_2469_, 7);
v_snapshotTasks_2477_ = lean_ctor_get(v___x_2469_, 8);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v___x_2469_, 5);
lean_dec(v_unused_2532_);
v___x_2479_ = v___x_2469_;
v_isShared_2480_ = v_isSharedCheck_2531_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_snapshotTasks_2477_);
lean_inc(v_infoState_2476_);
lean_inc(v_messages_2475_);
lean_inc(v_traceState_2474_);
lean_inc(v_auxDeclNGen_2473_);
lean_inc(v_ngen_2472_);
lean_inc(v_nextMacroScope_2471_);
lean_inc(v_env_2470_);
lean_dec(v___x_2469_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2531_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2481_ = l_Lean_Environment_setExporting(v_env_2470_, v_isExporting_2460_);
v___x_2482_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 5, v___x_2482_);
lean_ctor_set(v___x_2479_, 0, v___x_2481_);
v___x_2484_ = v___x_2479_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_nextMacroScope_2471_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_ngen_2472_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_auxDeclNGen_2473_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_traceState_2474_);
lean_ctor_set(v_reuseFailAlloc_2530_, 5, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2530_, 6, v_messages_2475_);
lean_ctor_set(v_reuseFailAlloc_2530_, 7, v_infoState_2476_);
lean_ctor_set(v_reuseFailAlloc_2530_, 8, v_snapshotTasks_2477_);
v___x_2484_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_mctx_2487_; lean_object* v_zetaDeltaFVarIds_2488_; lean_object* v_postponed_2489_; lean_object* v_diag_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2528_; 
v___x_2485_ = lean_st_ref_set(v___y_2464_, v___x_2484_);
v___x_2486_ = lean_st_ref_take(v___y_2462_);
v_mctx_2487_ = lean_ctor_get(v___x_2486_, 0);
v_zetaDeltaFVarIds_2488_ = lean_ctor_get(v___x_2486_, 2);
v_postponed_2489_ = lean_ctor_get(v___x_2486_, 3);
v_diag_2490_ = lean_ctor_get(v___x_2486_, 4);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v___x_2486_, 1);
lean_dec(v_unused_2529_);
v___x_2492_ = v___x_2486_;
v_isShared_2493_ = v_isSharedCheck_2528_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_diag_2490_);
lean_inc(v_postponed_2489_);
lean_inc(v_zetaDeltaFVarIds_2488_);
lean_inc(v_mctx_2487_);
lean_dec(v___x_2486_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2528_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2494_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 1, v___x_2494_);
v___x_2496_ = v___x_2492_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_mctx_2487_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_zetaDeltaFVarIds_2488_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v_postponed_2489_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_diag_2490_);
v___x_2496_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v_r_2498_; 
v___x_2497_ = lean_st_ref_set(v___y_2462_, v___x_2496_);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
v_r_2498_ = lean_apply_5(v_x_2459_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, lean_box(0));
if (lean_obj_tag(v_r_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2515_; 
v_a_2499_ = lean_ctor_get(v_r_2498_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_r_2498_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2501_ = v_r_2498_;
v_isShared_2502_ = v_isSharedCheck_2515_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v_r_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2515_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
lean_inc(v_a_2499_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 1);
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v___x_2505_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2464_, v_isExporting_2468_, v___x_2482_, v___y_2462_, v___x_2494_, v___x_2504_);
lean_dec_ref(v___x_2504_);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2505_, 0);
lean_dec(v_unused_2513_);
v___x_2507_ = v___x_2505_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_dec(v___x_2505_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v_a_2499_);
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2499_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_a_2516_ = lean_ctor_get(v_r_2498_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v_r_2498_);
v___x_2517_ = lean_box(0);
v___x_2518_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2464_, v_isExporting_2468_, v___x_2482_, v___y_2462_, v___x_2494_, v___x_2517_);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v___x_2518_, 0);
lean_dec(v_unused_2526_);
v___x_2520_ = v___x_2518_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v___x_2518_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set_tag(v___x_2520_, 1);
lean_ctor_set(v___x_2520_, 0, v_a_2516_);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2516_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2533_, lean_object* v_isExporting_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
uint8_t v_isExporting_boxed_2540_; lean_object* v_res_2541_; 
v_isExporting_boxed_2540_ = lean_unbox(v_isExporting_2534_);
v_res_2541_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2533_, v_isExporting_boxed_2540_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2542_, uint8_t v_when_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
if (v_when_2543_ == 0)
{
lean_object* v___x_2549_; 
lean_inc(v___y_2547_);
lean_inc_ref(v___y_2546_);
lean_inc(v___y_2545_);
lean_inc_ref(v___y_2544_);
v___x_2549_ = lean_apply_5(v_x_2542_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, lean_box(0));
return v___x_2549_;
}
else
{
uint8_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = 0;
v___x_2551_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2542_, v___x_2550_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2552_, lean_object* v_when_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
uint8_t v_when_boxed_2559_; lean_object* v_res_2560_; 
v_when_boxed_2559_ = lean_unbox(v_when_2553_);
v_res_2560_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2552_, v_when_boxed_2559_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v_res_2560_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2563_ = l_Lean_stringToMessageData(v___x_2562_);
return v___x_2563_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2566_ = l_Lean_stringToMessageData(v___x_2565_);
return v___x_2566_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2569_ = l_Lean_stringToMessageData(v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2570_, uint8_t v_nonRec_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; lean_object* v_env_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; 
v___x_2577_ = lean_st_ref_get(v___y_2575_);
v_env_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc_ref(v_env_2578_);
lean_dec(v___x_2577_);
v___x_2579_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2570_);
v___x_2580_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2578_, v_declName_2570_, v___x_2579_);
v___x_2581_ = lean_box(v_nonRec_2571_);
lean_inc(v___x_2580_);
v___f_2582_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2582_, 0, v___x_2580_);
lean_closure_set(v___f_2582_, 1, v_declName_2570_);
lean_closure_set(v___f_2582_, 2, v___x_2581_);
lean_closure_set(v___f_2582_, 3, v___x_2579_);
v___x_2583_ = 1;
v___x_2584_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2582_, v___x_2583_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
if (lean_obj_tag(v_a_2585_) == 1)
{
lean_object* v_val_2586_; uint8_t v___x_2587_; 
v_val_2586_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_val_2586_);
lean_dec_ref(v_a_2585_);
v___x_2587_ = lean_name_eq(v_val_2586_, v___x_2580_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec_ref(v___x_2584_);
v___x_2588_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2589_ = l_Lean_MessageData_ofName(v_val_2586_);
v___x_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = l_Lean_MessageData_ofName(v___x_2580_);
v___x_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2596_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_dec(v_val_2586_);
lean_dec(v___x_2580_);
return v___x_2584_;
}
}
else
{
lean_dec(v_a_2585_);
lean_dec(v___x_2580_);
return v___x_2584_;
}
}
else
{
lean_dec(v___x_2580_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2606_, lean_object* v_nonRec_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
uint8_t v_nonRec_boxed_2613_; lean_object* v_res_2614_; 
v_nonRec_boxed_2613_ = lean_unbox(v_nonRec_2607_);
v_res_2614_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2606_, v_nonRec_boxed_2613_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2615_, uint8_t v_nonRec_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2622_; lean_object* v___f_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2622_ = lean_box(v_nonRec_2616_);
v___f_2623_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2623_, 0, v_declName_2615_);
lean_closure_set(v___f_2623_, 1, v___x_2622_);
v___x_2624_ = lean_unsigned_to_nat(32u);
v___x_2625_ = lean_mk_empty_array_with_capacity(v___x_2624_);
lean_dec_ref(v___x_2625_);
v___x_2626_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2627_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2628_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2626_, v___x_2627_, v___f_2623_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2629_, lean_object* v_nonRec_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
uint8_t v_nonRec_boxed_2636_; lean_object* v_res_2637_; 
v_nonRec_boxed_2636_ = lean_unbox(v_nonRec_2630_);
v_res_2637_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2629_, v_nonRec_boxed_2636_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2638_, lean_object* v_as_2639_, lean_object* v_as_x27_2640_, lean_object* v_b_2641_, lean_object* v_a_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2638_, v_as_x27_2640_, v_b_2641_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2649_, lean_object* v_as_2650_, lean_object* v_as_x27_2651_, lean_object* v_b_2652_, lean_object* v_a_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2649_, v_as_2650_, v_as_x27_2651_, v_b_2652_, v_a_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v_as_x27_2651_);
lean_dec(v_as_2650_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2660_, lean_object* v_x_2661_, uint8_t v_isExporting_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2661_, v_isExporting_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2669_, lean_object* v_x_2670_, lean_object* v_isExporting_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
uint8_t v_isExporting_boxed_2677_; lean_object* v_res_2678_; 
v_isExporting_boxed_2677_ = lean_unbox(v_isExporting_2671_);
v_res_2678_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2669_, v_x_2670_, v_isExporting_boxed_2677_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2679_, lean_object* v_x_2680_, uint8_t v_when_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2680_, v_when_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2688_, lean_object* v_x_2689_, lean_object* v_when_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
uint8_t v_when_boxed_2696_; lean_object* v_res_2697_; 
v_when_boxed_2696_ = lean_unbox(v_when_2690_);
v_res_2697_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2688_, v_x_2689_, v_when_boxed_2696_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2698_, lean_object* v_msg_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_msg_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2706_, v_msg_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
return v_res_2713_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = lean_unsigned_to_nat(32u);
v___x_2715_ = lean_mk_empty_array_with_capacity(v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
return v___x_2716_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2717_ = ((size_t)5ULL);
v___x_2718_ = lean_unsigned_to_nat(0u);
v___x_2719_ = lean_unsigned_to_nat(32u);
v___x_2720_ = lean_mk_empty_array_with_capacity(v___x_2719_);
v___x_2721_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2722_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v___x_2720_);
lean_ctor_set(v___x_2722_, 2, v___x_2718_);
lean_ctor_set(v___x_2722_, 3, v___x_2718_);
lean_ctor_set_usize(v___x_2722_, 4, v___x_2717_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v_traceState_2726_; lean_object* v_traces_2727_; lean_object* v___x_2728_; lean_object* v_traceState_2729_; lean_object* v_env_2730_; lean_object* v_nextMacroScope_2731_; lean_object* v_ngen_2732_; lean_object* v_auxDeclNGen_2733_; lean_object* v_cache_2734_; lean_object* v_messages_2735_; lean_object* v_infoState_2736_; lean_object* v_snapshotTasks_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2756_; 
v___x_2725_ = lean_st_ref_get(v___y_2723_);
v_traceState_2726_ = lean_ctor_get(v___x_2725_, 4);
lean_inc_ref(v_traceState_2726_);
lean_dec(v___x_2725_);
v_traces_2727_ = lean_ctor_get(v_traceState_2726_, 0);
lean_inc_ref(v_traces_2727_);
lean_dec_ref(v_traceState_2726_);
v___x_2728_ = lean_st_ref_take(v___y_2723_);
v_traceState_2729_ = lean_ctor_get(v___x_2728_, 4);
v_env_2730_ = lean_ctor_get(v___x_2728_, 0);
v_nextMacroScope_2731_ = lean_ctor_get(v___x_2728_, 1);
v_ngen_2732_ = lean_ctor_get(v___x_2728_, 2);
v_auxDeclNGen_2733_ = lean_ctor_get(v___x_2728_, 3);
v_cache_2734_ = lean_ctor_get(v___x_2728_, 5);
v_messages_2735_ = lean_ctor_get(v___x_2728_, 6);
v_infoState_2736_ = lean_ctor_get(v___x_2728_, 7);
v_snapshotTasks_2737_ = lean_ctor_get(v___x_2728_, 8);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2739_ = v___x_2728_;
v_isShared_2740_ = v_isSharedCheck_2756_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_snapshotTasks_2737_);
lean_inc(v_infoState_2736_);
lean_inc(v_messages_2735_);
lean_inc(v_cache_2734_);
lean_inc(v_traceState_2729_);
lean_inc(v_auxDeclNGen_2733_);
lean_inc(v_ngen_2732_);
lean_inc(v_nextMacroScope_2731_);
lean_inc(v_env_2730_);
lean_dec(v___x_2728_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2756_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
uint64_t v_tid_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2754_; 
v_tid_2741_ = lean_ctor_get_uint64(v_traceState_2729_, sizeof(void*)*1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_traceState_2729_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v_traceState_2729_, 0);
lean_dec(v_unused_2755_);
v___x_2743_ = v_traceState_2729_;
v_isShared_2744_ = v_isSharedCheck_2754_;
goto v_resetjp_2742_;
}
else
{
lean_dec(v_traceState_2729_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2754_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2745_);
v___x_2747_ = v___x_2743_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2745_);
lean_ctor_set_uint64(v_reuseFailAlloc_2753_, sizeof(void*)*1, v_tid_2741_);
v___x_2747_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2749_; 
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 4, v___x_2747_);
v___x_2749_ = v___x_2739_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_env_2730_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_nextMacroScope_2731_);
lean_ctor_set(v_reuseFailAlloc_2752_, 2, v_ngen_2732_);
lean_ctor_set(v_reuseFailAlloc_2752_, 3, v_auxDeclNGen_2733_);
lean_ctor_set(v_reuseFailAlloc_2752_, 4, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2752_, 5, v_cache_2734_);
lean_ctor_set(v_reuseFailAlloc_2752_, 6, v_messages_2735_);
lean_ctor_set(v_reuseFailAlloc_2752_, 7, v_infoState_2736_);
lean_ctor_set(v_reuseFailAlloc_2752_, 8, v_snapshotTasks_2737_);
v___x_2749_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_st_ref_set(v___y_2723_, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_traces_2727_);
return v___x_2751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2757_);
lean_dec(v___y_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2761_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = 0;
v___x_2773_ = lean_box(v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
return v_res_2779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2782_ = l_Lean_stringToMessageData(v___x_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2783_, lean_object* v_x_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2789_ = l_Lean_MessageData_ofName(v_name_2783_);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2792_, lean_object* v_x_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2792_, v_x_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v_x_2793_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_x_2798_){
_start:
{
if (lean_obj_tag(v_x_2798_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_a_2800_ = lean_ctor_get(v_x_2798_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_x_2798_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v_x_2798_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v_x_2798_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set_tag(v___x_2802_, 1);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v_x_2798_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_x_2798_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v_x_2798_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v_x_2798_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 0);
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object* v_x_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_e_2819_){
_start:
{
if (lean_obj_tag(v_e_2819_) == 0)
{
uint8_t v___x_2820_; 
v___x_2820_ = 2;
return v___x_2820_;
}
else
{
lean_object* v_a_2821_; uint8_t v___x_2822_; 
v_a_2821_ = lean_ctor_get(v_e_2819_, 0);
v___x_2822_ = lean_unbox(v_a_2821_);
if (v___x_2822_ == 0)
{
uint8_t v___x_2823_; 
v___x_2823_ = 1;
return v___x_2823_;
}
else
{
uint8_t v___x_2824_; 
v___x_2824_ = 0;
return v___x_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_e_2825_){
_start:
{
uint8_t v_res_2826_; lean_object* v_r_2827_; 
v_res_2826_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_e_2825_);
lean_dec_ref(v_e_2825_);
v_r_2827_ = lean_box(v_res_2826_);
return v_r_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(size_t v_sz_2828_, size_t v_i_2829_, lean_object* v_bs_2830_){
_start:
{
uint8_t v___x_2831_; 
v___x_2831_ = lean_usize_dec_lt(v_i_2829_, v_sz_2828_);
if (v___x_2831_ == 0)
{
return v_bs_2830_;
}
else
{
lean_object* v_v_2832_; lean_object* v_msg_2833_; lean_object* v___x_2834_; lean_object* v_bs_x27_2835_; size_t v___x_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
v_v_2832_ = lean_array_uget_borrowed(v_bs_2830_, v_i_2829_);
v_msg_2833_ = lean_ctor_get(v_v_2832_, 1);
lean_inc_ref(v_msg_2833_);
v___x_2834_ = lean_unsigned_to_nat(0u);
v_bs_x27_2835_ = lean_array_uset(v_bs_2830_, v_i_2829_, v___x_2834_);
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = lean_usize_add(v_i_2829_, v___x_2836_);
v___x_2838_ = lean_array_uset(v_bs_x27_2835_, v_i_2829_, v_msg_2833_);
v_i_2829_ = v___x_2837_;
v_bs_2830_ = v___x_2838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_sz_2840_, lean_object* v_i_2841_, lean_object* v_bs_2842_){
_start:
{
size_t v_sz_boxed_2843_; size_t v_i_boxed_2844_; lean_object* v_res_2845_; 
v_sz_boxed_2843_ = lean_unbox_usize(v_sz_2840_);
lean_dec(v_sz_2840_);
v_i_boxed_2844_ = lean_unbox_usize(v_i_2841_);
lean_dec(v_i_2841_);
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_boxed_2843_, v_i_boxed_2844_, v_bs_2842_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_oldTraces_2846_, lean_object* v_data_2847_, lean_object* v_ref_2848_, lean_object* v_msg_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_fileName_2853_; lean_object* v_fileMap_2854_; lean_object* v_options_2855_; lean_object* v_currRecDepth_2856_; lean_object* v_maxRecDepth_2857_; lean_object* v_ref_2858_; lean_object* v_currNamespace_2859_; lean_object* v_openDecls_2860_; lean_object* v_initHeartbeats_2861_; lean_object* v_maxHeartbeats_2862_; lean_object* v_quotContext_2863_; lean_object* v_currMacroScope_2864_; uint8_t v_diag_2865_; lean_object* v_cancelTk_x3f_2866_; uint8_t v_suppressElabErrors_2867_; lean_object* v_inheritedTraceOptions_2868_; lean_object* v___x_2869_; lean_object* v_traceState_2870_; lean_object* v_traces_2871_; lean_object* v_ref_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; size_t v_sz_2875_; size_t v___x_2876_; lean_object* v___x_2877_; lean_object* v_msg_2878_; lean_object* v___x_2879_; lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2917_; 
v_fileName_2853_ = lean_ctor_get(v___y_2850_, 0);
v_fileMap_2854_ = lean_ctor_get(v___y_2850_, 1);
v_options_2855_ = lean_ctor_get(v___y_2850_, 2);
v_currRecDepth_2856_ = lean_ctor_get(v___y_2850_, 3);
v_maxRecDepth_2857_ = lean_ctor_get(v___y_2850_, 4);
v_ref_2858_ = lean_ctor_get(v___y_2850_, 5);
v_currNamespace_2859_ = lean_ctor_get(v___y_2850_, 6);
v_openDecls_2860_ = lean_ctor_get(v___y_2850_, 7);
v_initHeartbeats_2861_ = lean_ctor_get(v___y_2850_, 8);
v_maxHeartbeats_2862_ = lean_ctor_get(v___y_2850_, 9);
v_quotContext_2863_ = lean_ctor_get(v___y_2850_, 10);
v_currMacroScope_2864_ = lean_ctor_get(v___y_2850_, 11);
v_diag_2865_ = lean_ctor_get_uint8(v___y_2850_, sizeof(void*)*14);
v_cancelTk_x3f_2866_ = lean_ctor_get(v___y_2850_, 12);
v_suppressElabErrors_2867_ = lean_ctor_get_uint8(v___y_2850_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2868_ = lean_ctor_get(v___y_2850_, 13);
v___x_2869_ = lean_st_ref_get(v___y_2851_);
v_traceState_2870_ = lean_ctor_get(v___x_2869_, 4);
lean_inc_ref(v_traceState_2870_);
lean_dec(v___x_2869_);
v_traces_2871_ = lean_ctor_get(v_traceState_2870_, 0);
lean_inc_ref(v_traces_2871_);
lean_dec_ref(v_traceState_2870_);
v_ref_2872_ = l_Lean_replaceRef(v_ref_2848_, v_ref_2858_);
lean_inc_ref(v_inheritedTraceOptions_2868_);
lean_inc(v_cancelTk_x3f_2866_);
lean_inc(v_currMacroScope_2864_);
lean_inc(v_quotContext_2863_);
lean_inc(v_maxHeartbeats_2862_);
lean_inc(v_initHeartbeats_2861_);
lean_inc(v_openDecls_2860_);
lean_inc(v_currNamespace_2859_);
lean_inc(v_maxRecDepth_2857_);
lean_inc(v_currRecDepth_2856_);
lean_inc_ref(v_options_2855_);
lean_inc_ref(v_fileMap_2854_);
lean_inc_ref(v_fileName_2853_);
v___x_2873_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2873_, 0, v_fileName_2853_);
lean_ctor_set(v___x_2873_, 1, v_fileMap_2854_);
lean_ctor_set(v___x_2873_, 2, v_options_2855_);
lean_ctor_set(v___x_2873_, 3, v_currRecDepth_2856_);
lean_ctor_set(v___x_2873_, 4, v_maxRecDepth_2857_);
lean_ctor_set(v___x_2873_, 5, v_ref_2872_);
lean_ctor_set(v___x_2873_, 6, v_currNamespace_2859_);
lean_ctor_set(v___x_2873_, 7, v_openDecls_2860_);
lean_ctor_set(v___x_2873_, 8, v_initHeartbeats_2861_);
lean_ctor_set(v___x_2873_, 9, v_maxHeartbeats_2862_);
lean_ctor_set(v___x_2873_, 10, v_quotContext_2863_);
lean_ctor_set(v___x_2873_, 11, v_currMacroScope_2864_);
lean_ctor_set(v___x_2873_, 12, v_cancelTk_x3f_2866_);
lean_ctor_set(v___x_2873_, 13, v_inheritedTraceOptions_2868_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*14, v_diag_2865_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*14 + 1, v_suppressElabErrors_2867_);
v___x_2874_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2871_);
lean_dec_ref(v_traces_2871_);
v_sz_2875_ = lean_array_size(v___x_2874_);
v___x_2876_ = ((size_t)0ULL);
v___x_2877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_2875_, v___x_2876_, v___x_2874_);
v_msg_2878_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2878_, 0, v_data_2847_);
lean_ctor_set(v_msg_2878_, 1, v_msg_2849_);
lean_ctor_set(v_msg_2878_, 2, v___x_2877_);
v___x_2879_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2878_, v___x_2873_, v___y_2851_);
lean_dec_ref(v___x_2873_);
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2917_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2917_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v_traceState_2885_; lean_object* v_env_2886_; lean_object* v_nextMacroScope_2887_; lean_object* v_ngen_2888_; lean_object* v_auxDeclNGen_2889_; lean_object* v_cache_2890_; lean_object* v_messages_2891_; lean_object* v_infoState_2892_; lean_object* v_snapshotTasks_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2916_; 
v___x_2884_ = lean_st_ref_take(v___y_2851_);
v_traceState_2885_ = lean_ctor_get(v___x_2884_, 4);
v_env_2886_ = lean_ctor_get(v___x_2884_, 0);
v_nextMacroScope_2887_ = lean_ctor_get(v___x_2884_, 1);
v_ngen_2888_ = lean_ctor_get(v___x_2884_, 2);
v_auxDeclNGen_2889_ = lean_ctor_get(v___x_2884_, 3);
v_cache_2890_ = lean_ctor_get(v___x_2884_, 5);
v_messages_2891_ = lean_ctor_get(v___x_2884_, 6);
v_infoState_2892_ = lean_ctor_get(v___x_2884_, 7);
v_snapshotTasks_2893_ = lean_ctor_get(v___x_2884_, 8);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2895_ = v___x_2884_;
v_isShared_2896_ = v_isSharedCheck_2916_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_snapshotTasks_2893_);
lean_inc(v_infoState_2892_);
lean_inc(v_messages_2891_);
lean_inc(v_cache_2890_);
lean_inc(v_traceState_2885_);
lean_inc(v_auxDeclNGen_2889_);
lean_inc(v_ngen_2888_);
lean_inc(v_nextMacroScope_2887_);
lean_inc(v_env_2886_);
lean_dec(v___x_2884_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2916_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
uint64_t v_tid_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2914_; 
v_tid_2897_ = lean_ctor_get_uint64(v_traceState_2885_, sizeof(void*)*1);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_traceState_2885_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v_traceState_2885_, 0);
lean_dec(v_unused_2915_);
v___x_2899_ = v_traceState_2885_;
v_isShared_2900_ = v_isSharedCheck_2914_;
goto v_resetjp_2898_;
}
else
{
lean_dec(v_traceState_2885_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2914_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2901_, 0, v_ref_2848_);
lean_ctor_set(v___x_2901_, 1, v_a_2880_);
v___x_2902_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2846_, v___x_2901_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2902_);
v___x_2904_ = v___x_2899_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2902_);
lean_ctor_set_uint64(v_reuseFailAlloc_2913_, sizeof(void*)*1, v_tid_2897_);
v___x_2904_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2906_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 4, v___x_2904_);
v___x_2906_ = v___x_2895_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_env_2886_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_nextMacroScope_2887_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_ngen_2888_);
lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_auxDeclNGen_2889_);
lean_ctor_set(v_reuseFailAlloc_2912_, 4, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2912_, 5, v_cache_2890_);
lean_ctor_set(v_reuseFailAlloc_2912_, 6, v_messages_2891_);
lean_ctor_set(v_reuseFailAlloc_2912_, 7, v_infoState_2892_);
lean_ctor_set(v_reuseFailAlloc_2912_, 8, v_snapshotTasks_2893_);
v___x_2906_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2907_ = lean_st_ref_set(v___y_2851_, v___x_2906_);
v___x_2908_ = lean_box(0);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2908_);
v___x_2910_ = v___x_2882_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_oldTraces_2918_, lean_object* v_data_2919_, lean_object* v_ref_2920_, lean_object* v_msg_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2918_, v_data_2919_, v_ref_2920_, v_msg_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2925_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2928_ = l_Lean_stringToMessageData(v___x_2927_);
return v___x_2928_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2));
v___x_2931_ = l_Lean_stringToMessageData(v___x_2930_);
return v___x_2931_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4(void){
_start:
{
lean_object* v___x_2932_; double v___x_2933_; 
v___x_2932_ = lean_unsigned_to_nat(1000u);
v___x_2933_ = lean_float_of_nat(v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2934_, uint8_t v_collapsed_2935_, lean_object* v_tag_2936_, lean_object* v_opts_2937_, uint8_t v_clsEnabled_2938_, lean_object* v_oldTraces_2939_, lean_object* v_msg_2940_, lean_object* v_resStartStop_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3044_; 
v_fst_2945_ = lean_ctor_get(v_resStartStop_2941_, 0);
v_snd_2946_ = lean_ctor_get(v_resStartStop_2941_, 1);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_resStartStop_2941_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_2948_ = v_resStartStop_2941_;
v_isShared_2949_ = v_isSharedCheck_3044_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_snd_2946_);
lean_inc(v_fst_2945_);
lean_dec(v_resStartStop_2941_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3044_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v_data_2953_; lean_object* v_fst_2964_; lean_object* v_snd_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3043_; 
v_fst_2964_ = lean_ctor_get(v_snd_2946_, 0);
v_snd_2965_ = lean_ctor_get(v_snd_2946_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_snd_2946_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_2967_ = v_snd_2946_;
v_isShared_2968_ = v_isSharedCheck_3043_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_snd_2965_);
lean_inc(v_fst_2964_);
lean_dec(v_snd_2946_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3043_;
goto v_resetjp_2966_;
}
v___jp_2950_:
{
lean_object* v___x_2954_; 
lean_inc(v___y_2951_);
v___x_2954_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_2939_, v_data_2953_, v___y_2951_, v___y_2952_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v___x_2955_; 
lean_dec_ref(v___x_2954_);
v___x_2955_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2945_);
return v___x_2955_;
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_fst_2945_);
v_a_2956_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2954_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2954_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; lean_object* v___y_2972_; lean_object* v_a_2973_; uint8_t v___y_2997_; double v___y_3028_; 
v___x_2969_ = l_Lean_trace_profiler;
v___x_2970_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2937_, v___x_2969_);
if (v___x_2970_ == 0)
{
v___y_2997_ = v___x_2970_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3034_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2937_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; double v___x_3037_; double v___x_3038_; double v___x_3039_; 
v___x_3035_ = l_Lean_trace_profiler_threshold;
v___x_3036_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2937_, v___x_3035_);
v___x_3037_ = lean_float_of_nat(v___x_3036_);
v___x_3038_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4);
v___x_3039_ = lean_float_div(v___x_3037_, v___x_3038_);
v___y_3028_ = v___x_3039_;
goto v___jp_3027_;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; double v___x_3042_; 
v___x_3040_ = l_Lean_trace_profiler_threshold;
v___x_3041_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2937_, v___x_3040_);
v___x_3042_ = lean_float_of_nat(v___x_3041_);
v___y_3028_ = v___x_3042_;
goto v___jp_3027_;
}
}
v___jp_2971_:
{
uint8_t v_result_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v_result_2974_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_fst_2945_);
v___x_2975_ = l_Lean_TraceResult_toEmoji(v_result_2974_);
v___x_2976_ = l_Lean_stringToMessageData(v___x_2975_);
v___x_2977_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 7);
lean_ctor_set(v___x_2967_, 1, v___x_2977_);
lean_ctor_set(v___x_2967_, 0, v___x_2976_);
v___x_2979_ = v___x_2967_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v_m_2981_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set_tag(v___x_2948_, 7);
lean_ctor_set(v___x_2948_, 1, v_a_2973_);
lean_ctor_set(v___x_2948_, 0, v___x_2979_);
v_m_2981_ = v___x_2948_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_a_2973_);
v_m_2981_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; double v___x_2984_; lean_object* v_data_2985_; 
v___x_2982_ = lean_box(v_result_2974_);
v___x_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
v___x_2984_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2936_);
lean_inc_ref(v___x_2983_);
lean_inc(v_cls_2934_);
v_data_2985_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2985_, 0, v_cls_2934_);
lean_ctor_set(v_data_2985_, 1, v___x_2983_);
lean_ctor_set(v_data_2985_, 2, v_tag_2936_);
lean_ctor_set_float(v_data_2985_, sizeof(void*)*3, v___x_2984_);
lean_ctor_set_float(v_data_2985_, sizeof(void*)*3 + 8, v___x_2984_);
lean_ctor_set_uint8(v_data_2985_, sizeof(void*)*3 + 16, v_collapsed_2935_);
if (v___x_2970_ == 0)
{
lean_dec_ref(v___x_2983_);
lean_dec(v_snd_2965_);
lean_dec(v_fst_2964_);
lean_dec_ref(v_tag_2936_);
lean_dec(v_cls_2934_);
v___y_2951_ = v___y_2972_;
v___y_2952_ = v_m_2981_;
v_data_2953_ = v_data_2985_;
goto v___jp_2950_;
}
else
{
lean_object* v_data_2986_; double v___x_2987_; double v___x_2988_; 
lean_dec_ref(v_data_2985_);
v_data_2986_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2986_, 0, v_cls_2934_);
lean_ctor_set(v_data_2986_, 1, v___x_2983_);
lean_ctor_set(v_data_2986_, 2, v_tag_2936_);
v___x_2987_ = lean_unbox_float(v_fst_2964_);
lean_dec(v_fst_2964_);
lean_ctor_set_float(v_data_2986_, sizeof(void*)*3, v___x_2987_);
v___x_2988_ = lean_unbox_float(v_snd_2965_);
lean_dec(v_snd_2965_);
lean_ctor_set_float(v_data_2986_, sizeof(void*)*3 + 8, v___x_2988_);
lean_ctor_set_uint8(v_data_2986_, sizeof(void*)*3 + 16, v_collapsed_2935_);
v___y_2951_ = v___y_2972_;
v___y_2952_ = v_m_2981_;
v_data_2953_ = v_data_2986_;
goto v___jp_2950_;
}
}
}
}
v___jp_2991_:
{
lean_object* v_ref_2992_; lean_object* v___x_2993_; 
v_ref_2992_ = lean_ctor_get(v___y_2942_, 5);
lean_inc(v___y_2943_);
lean_inc_ref(v___y_2942_);
lean_inc(v_fst_2945_);
v___x_2993_ = lean_apply_4(v_msg_2940_, v_fst_2945_, v___y_2942_, v___y_2943_, lean_box(0));
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref(v___x_2993_);
v___y_2972_ = v_ref_2992_;
v_a_2973_ = v_a_2994_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_2995_; 
lean_dec_ref(v___x_2993_);
v___x_2995_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3);
v___y_2972_ = v_ref_2992_;
v_a_2973_ = v___x_2995_;
goto v___jp_2971_;
}
}
v___jp_2996_:
{
if (v_clsEnabled_2938_ == 0)
{
if (v___y_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v_traceState_2999_; lean_object* v_env_3000_; lean_object* v_nextMacroScope_3001_; lean_object* v_ngen_3002_; lean_object* v_auxDeclNGen_3003_; lean_object* v_cache_3004_; lean_object* v_messages_3005_; lean_object* v_infoState_3006_; lean_object* v_snapshotTasks_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3026_; 
lean_del_object(v___x_2967_);
lean_dec(v_snd_2965_);
lean_dec(v_fst_2964_);
lean_del_object(v___x_2948_);
lean_dec_ref(v_msg_2940_);
lean_dec_ref(v_tag_2936_);
lean_dec(v_cls_2934_);
v___x_2998_ = lean_st_ref_take(v___y_2943_);
v_traceState_2999_ = lean_ctor_get(v___x_2998_, 4);
v_env_3000_ = lean_ctor_get(v___x_2998_, 0);
v_nextMacroScope_3001_ = lean_ctor_get(v___x_2998_, 1);
v_ngen_3002_ = lean_ctor_get(v___x_2998_, 2);
v_auxDeclNGen_3003_ = lean_ctor_get(v___x_2998_, 3);
v_cache_3004_ = lean_ctor_get(v___x_2998_, 5);
v_messages_3005_ = lean_ctor_get(v___x_2998_, 6);
v_infoState_3006_ = lean_ctor_get(v___x_2998_, 7);
v_snapshotTasks_3007_ = lean_ctor_get(v___x_2998_, 8);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3009_ = v___x_2998_;
v_isShared_3010_ = v_isSharedCheck_3026_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_snapshotTasks_3007_);
lean_inc(v_infoState_3006_);
lean_inc(v_messages_3005_);
lean_inc(v_cache_3004_);
lean_inc(v_traceState_2999_);
lean_inc(v_auxDeclNGen_3003_);
lean_inc(v_ngen_3002_);
lean_inc(v_nextMacroScope_3001_);
lean_inc(v_env_3000_);
lean_dec(v___x_2998_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3026_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
uint64_t v_tid_3011_; lean_object* v_traces_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3025_; 
v_tid_3011_ = lean_ctor_get_uint64(v_traceState_2999_, sizeof(void*)*1);
v_traces_3012_ = lean_ctor_get(v_traceState_2999_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_traceState_2999_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3014_ = v_traceState_2999_;
v_isShared_3015_ = v_isSharedCheck_3025_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_traces_3012_);
lean_dec(v_traceState_2999_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3025_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3016_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2939_, v_traces_3012_);
lean_dec_ref(v_traces_3012_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3016_);
v___x_3018_ = v___x_3014_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3016_);
lean_ctor_set_uint64(v_reuseFailAlloc_3024_, sizeof(void*)*1, v_tid_3011_);
v___x_3018_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3020_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 4, v___x_3018_);
v___x_3020_ = v___x_3009_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_env_3000_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_nextMacroScope_3001_);
lean_ctor_set(v_reuseFailAlloc_3023_, 2, v_ngen_3002_);
lean_ctor_set(v_reuseFailAlloc_3023_, 3, v_auxDeclNGen_3003_);
lean_ctor_set(v_reuseFailAlloc_3023_, 4, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3023_, 5, v_cache_3004_);
lean_ctor_set(v_reuseFailAlloc_3023_, 6, v_messages_3005_);
lean_ctor_set(v_reuseFailAlloc_3023_, 7, v_infoState_3006_);
lean_ctor_set(v_reuseFailAlloc_3023_, 8, v_snapshotTasks_3007_);
v___x_3020_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = lean_st_ref_set(v___y_2943_, v___x_3020_);
v___x_3022_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_2945_);
return v___x_3022_;
}
}
}
}
}
else
{
goto v___jp_2991_;
}
}
else
{
goto v___jp_2991_;
}
}
v___jp_3027_:
{
double v___x_3029_; double v___x_3030_; double v___x_3031_; uint8_t v___x_3032_; 
v___x_3029_ = lean_unbox_float(v_snd_2965_);
v___x_3030_ = lean_unbox_float(v_fst_2964_);
v___x_3031_ = lean_float_sub(v___x_3029_, v___x_3030_);
v___x_3032_ = lean_float_decLt(v___y_3028_, v___x_3031_);
v___y_2997_ = v___x_3032_;
goto v___jp_2996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3045_, lean_object* v_collapsed_3046_, lean_object* v_tag_3047_, lean_object* v_opts_3048_, lean_object* v_clsEnabled_3049_, lean_object* v_oldTraces_3050_, lean_object* v_msg_3051_, lean_object* v_resStartStop_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
uint8_t v_collapsed_boxed_3056_; uint8_t v_clsEnabled_boxed_3057_; lean_object* v_res_3058_; 
v_collapsed_boxed_3056_ = lean_unbox(v_collapsed_3046_);
v_clsEnabled_boxed_3057_ = lean_unbox(v_clsEnabled_3049_);
v_res_3058_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3045_, v_collapsed_boxed_3056_, v_tag_3047_, v_opts_3048_, v_clsEnabled_boxed_3057_, v_oldTraces_3050_, v_msg_3051_, v_resStartStop_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec_ref(v_opts_3048_);
return v_res_3058_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
lean_ctor_set(v___x_3063_, 2, v___x_3062_);
lean_ctor_set(v___x_3063_, 3, v___x_3062_);
lean_ctor_set(v___x_3063_, 4, v___x_3061_);
lean_ctor_set(v___x_3063_, 5, v___x_3061_);
lean_ctor_set(v___x_3063_, 6, v___x_3061_);
lean_ctor_set(v___x_3063_, 7, v___x_3061_);
lean_ctor_set(v___x_3063_, 8, v___x_3061_);
lean_ctor_set(v___x_3063_, 9, v___x_3061_);
return v___x_3063_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3065_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
lean_ctor_set(v___x_3065_, 2, v___x_3064_);
lean_ctor_set(v___x_3065_, 3, v___x_3064_);
lean_ctor_set(v___x_3065_, 4, v___x_3064_);
lean_ctor_set(v___x_3065_, 5, v___x_3064_);
return v___x_3065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
lean_ctor_set(v___x_3067_, 2, v___x_3066_);
lean_ctor_set(v___x_3067_, 3, v___x_3066_);
lean_ctor_set(v___x_3067_, 4, v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3068_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3069_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3070_ = lean_box(1);
v___x_3071_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3071_);
lean_ctor_set(v___x_3073_, 2, v___x_3070_);
lean_ctor_set(v___x_3073_, 3, v___x_3069_);
lean_ctor_set(v___x_3073_, 4, v___x_3068_);
return v___x_3073_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3079_ = l_Lean_Name_append(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3080_; double v___x_3081_; 
v___x_3080_ = lean_unsigned_to_nat(1000000000u);
v___x_3081_ = lean_float_of_nat(v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_3082_, lean_object* v_name_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_options_3087_; uint8_t v_hasTrace_3088_; 
v_options_3087_ = lean_ctor_get(v___y_3084_, 2);
v_hasTrace_3088_ = lean_ctor_get_uint8(v_options_3087_, sizeof(void*)*1);
if (v_hasTrace_3088_ == 0)
{
lean_object* v___x_3089_; lean_object* v_env_3090_; lean_object* v___x_3091_; 
lean_dec_ref(v___f_3082_);
v___x_3089_ = lean_st_ref_get(v___y_3085_);
v_env_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc_ref(v_env_3090_);
lean_dec(v___x_3089_);
lean_inc(v_name_3083_);
v___x_3091_ = l_Lean_Meta_declFromEqLikeName(v_env_3090_, v_name_3083_);
if (lean_obj_tag(v___x_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3191_; 
v_val_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3191_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_val_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3191_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_fst_3096_; lean_object* v_snd_3097_; lean_object* v___x_3098_; lean_object* v_env_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_fst_3096_ = lean_ctor_get(v_val_3092_, 0);
lean_inc_n(v_fst_3096_, 2);
v_snd_3097_ = lean_ctor_get(v_val_3092_, 1);
lean_inc_n(v_snd_3097_, 2);
lean_dec(v_val_3092_);
v___x_3098_ = lean_st_ref_get(v___y_3085_);
v_env_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc_ref(v_env_3099_);
lean_dec(v___x_3098_);
v___x_3100_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3099_, v_fst_3096_, v_snd_3097_);
v___x_3101_ = lean_name_eq(v_name_3083_, v___x_3100_);
lean_dec(v___x_3100_);
lean_dec(v_name_3083_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
lean_dec(v_snd_3097_);
lean_dec(v_fst_3096_);
v___x_3102_ = lean_box(v_hasTrace_3088_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3102_);
v___x_3104_ = v___x_3094_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
else
{
uint8_t v___x_3106_; lean_object* v_a_3108_; 
lean_inc(v_snd_3097_);
v___x_3106_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3097_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3122_; uint8_t v___x_3123_; lean_object* v_a_3125_; 
lean_del_object(v___x_3094_);
v___x_3122_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3123_ = lean_string_dec_eq(v_snd_3097_, v___x_3122_);
lean_dec(v_snd_3097_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_dec(v_fst_3096_);
v___x_3137_ = lean_box(v_hasTrace_3088_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
else
{
uint8_t v___x_3139_; uint8_t v___x_3140_; uint8_t v___x_3141_; lean_object* v___x_3142_; uint64_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3139_ = 1;
v___x_3140_ = 0;
v___x_3141_ = 2;
v___x_3142_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3142_, 0, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3142_, 1, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3142_, 2, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3142_, 3, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3142_, 4, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3142_, 5, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 6, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 7, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3142_, 8, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 9, v___x_3139_);
lean_ctor_set_uint8(v___x_3142_, 10, v___x_3140_);
lean_ctor_set_uint8(v___x_3142_, 11, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 12, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 13, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 14, v___x_3141_);
lean_ctor_set_uint8(v___x_3142_, 15, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 16, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 17, v___x_3123_);
lean_ctor_set_uint8(v___x_3142_, 18, v___x_3123_);
v___x_3143_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set_uint64(v___x_3144_, sizeof(void*)*1, v___x_3143_);
v___x_3145_ = lean_box(1);
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3148_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3150_, 0, v___x_3144_);
lean_ctor_set(v___x_3150_, 1, v___x_3145_);
lean_ctor_set(v___x_3150_, 2, v___x_3147_);
lean_ctor_set(v___x_3150_, 3, v___x_3148_);
lean_ctor_set(v___x_3150_, 4, v___x_3149_);
lean_ctor_set(v___x_3150_, 5, v___x_3146_);
lean_ctor_set(v___x_3150_, 6, v___x_3149_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*7, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*7 + 1, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*7 + 2, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*7 + 3, v___x_3101_);
v___x_3151_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3152_ = lean_st_mk_ref(v___x_3151_);
v___x_3153_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3096_, v___x_3101_, v___x_3150_, v___x_3152_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___x_3150_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref(v___x_3153_);
v___x_3155_ = lean_st_ref_get(v___x_3152_);
lean_dec(v___x_3152_);
lean_dec(v___x_3155_);
v_a_3125_ = v_a_3154_;
goto v___jp_3124_;
}
else
{
lean_dec(v___x_3152_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3156_; 
v_a_3156_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3156_);
lean_dec_ref(v___x_3153_);
v_a_3125_ = v_a_3156_;
goto v___jp_3124_;
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
v_a_3157_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3153_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3153_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
v___jp_3124_:
{
if (lean_obj_tag(v_a_3125_) == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = lean_box(v_hasTrace_3088_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
return v___x_3127_;
}
else
{
lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3135_; 
v_isSharedCheck_3135_ = !lean_is_exclusive(v_a_3125_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v_a_3125_, 0);
lean_dec(v_unused_3136_);
v___x_3129_ = v_a_3125_;
v_isShared_3130_ = v_isSharedCheck_3135_;
goto v_resetjp_3128_;
}
else
{
lean_dec(v_a_3125_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3135_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3131_ = lean_box(v___x_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3131_);
v___x_3133_ = v___x_3129_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
}
else
{
uint8_t v___x_3165_; uint8_t v___x_3166_; uint8_t v___x_3167_; lean_object* v___x_3168_; uint64_t v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v_snd_3097_);
v___x_3165_ = 1;
v___x_3166_ = 0;
v___x_3167_ = 2;
v___x_3168_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3168_, 0, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3168_, 1, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3168_, 2, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3168_, 3, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3168_, 4, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3168_, 5, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 6, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 7, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3168_, 8, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 9, v___x_3165_);
lean_ctor_set_uint8(v___x_3168_, 10, v___x_3166_);
lean_ctor_set_uint8(v___x_3168_, 11, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 12, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 13, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 14, v___x_3167_);
lean_ctor_set_uint8(v___x_3168_, 15, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 16, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 17, v___x_3106_);
lean_ctor_set_uint8(v___x_3168_, 18, v___x_3106_);
v___x_3169_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3168_);
v___x_3170_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set_uint64(v___x_3170_, sizeof(void*)*1, v___x_3169_);
v___x_3171_ = lean_box(1);
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3174_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3175_ = lean_box(0);
v___x_3176_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3176_, 0, v___x_3170_);
lean_ctor_set(v___x_3176_, 1, v___x_3171_);
lean_ctor_set(v___x_3176_, 2, v___x_3173_);
lean_ctor_set(v___x_3176_, 3, v___x_3174_);
lean_ctor_set(v___x_3176_, 4, v___x_3175_);
lean_ctor_set(v___x_3176_, 5, v___x_3172_);
lean_ctor_set(v___x_3176_, 6, v___x_3175_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*7, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*7 + 1, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*7 + 2, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*7 + 3, v___x_3101_);
v___x_3177_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3178_ = lean_st_mk_ref(v___x_3177_);
v___x_3179_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3096_, v___x_3176_, v___x_3178_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___x_3176_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3181_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
v___x_3181_ = lean_st_ref_get(v___x_3178_);
lean_dec(v___x_3178_);
lean_dec(v___x_3181_);
v_a_3108_ = v_a_3180_;
goto v___jp_3107_;
}
else
{
lean_dec(v___x_3178_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3182_; 
v_a_3182_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3182_);
lean_dec_ref(v___x_3179_);
v_a_3108_ = v_a_3182_;
goto v___jp_3107_;
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_del_object(v___x_3094_);
v_a_3183_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3179_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3179_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
v___jp_3107_:
{
if (lean_obj_tag(v_a_3108_) == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = lean_box(v_hasTrace_3088_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3109_);
v___x_3111_ = v___x_3094_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
else
{
lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
lean_del_object(v___x_3094_);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_a_3108_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v_a_3108_, 0);
lean_dec(v_unused_3121_);
v___x_3114_ = v_a_3108_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_dec(v_a_3108_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_box(v___x_3106_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set_tag(v___x_3114_, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_dec(v___x_3091_);
lean_dec(v_name_3083_);
v___x_3192_ = lean_box(v_hasTrace_3088_);
v___x_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
return v___x_3193_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3194_; lean_object* v___f_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v_a_3203_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v_a_3218_; lean_object* v___y_3222_; lean_object* v___y_3223_; uint8_t v___y_3224_; lean_object* v_a_3225_; lean_object* v___y_3227_; lean_object* v___y_3228_; uint8_t v___y_3229_; lean_object* v_a_3230_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v_a_3234_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v_a_3239_; lean_object* v___y_3249_; lean_object* v___y_3250_; uint8_t v_a_3251_; uint8_t v___y_3255_; uint8_t v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v_a_3259_; uint8_t v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v_a_3264_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v_a_3269_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; 
v_inheritedTraceOptions_3194_ = lean_ctor_get(v___y_3084_, 13);
lean_inc(v_name_3083_);
v___f_3195_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3195_, 0, v_name_3083_);
v___x_3196_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3197_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3198_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3199_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3194_, v_options_3087_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3394_; uint8_t v___x_3395_; lean_object* v_a_3397_; lean_object* v_a_3410_; 
v___x_3394_ = l_Lean_trace_profiler;
v___x_3395_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3087_, v___x_3394_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3422_; lean_object* v_env_3423_; lean_object* v___x_3424_; 
lean_dec_ref(v___f_3195_);
lean_dec_ref(v___f_3082_);
v___x_3422_ = lean_st_ref_get(v___y_3085_);
v_env_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc_ref(v_env_3423_);
lean_dec(v___x_3422_);
lean_inc(v_name_3083_);
v___x_3424_ = l_Lean_Meta_declFromEqLikeName(v_env_3423_, v_name_3083_);
if (lean_obj_tag(v___x_3424_) == 1)
{
lean_object* v_val_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3498_; 
v_val_3425_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3427_ = v___x_3424_;
v_isShared_3428_ = v_isSharedCheck_3498_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_val_3425_);
lean_dec(v___x_3424_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3498_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v_fst_3429_; lean_object* v_snd_3430_; lean_object* v___x_3431_; lean_object* v_env_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_fst_3429_ = lean_ctor_get(v_val_3425_, 0);
lean_inc_n(v_fst_3429_, 2);
v_snd_3430_ = lean_ctor_get(v_val_3425_, 1);
lean_inc_n(v_snd_3430_, 2);
lean_dec(v_val_3425_);
v___x_3431_ = lean_st_ref_get(v___y_3085_);
v_env_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc_ref(v_env_3432_);
lean_dec(v___x_3431_);
v___x_3433_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3432_, v_fst_3429_, v_snd_3430_);
v___x_3434_ = lean_name_eq(v_name_3083_, v___x_3433_);
lean_dec(v___x_3433_);
lean_dec(v_name_3083_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_dec(v_snd_3430_);
lean_dec(v_fst_3429_);
v___x_3435_ = lean_box(v___x_3395_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3435_);
v___x_3437_ = v___x_3427_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
else
{
uint8_t v___x_3439_; 
lean_inc(v_snd_3430_);
v___x_3439_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3430_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3440_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3441_ = lean_string_dec_eq(v_snd_3430_, v___x_3440_);
lean_dec(v_snd_3430_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
lean_dec(v_fst_3429_);
v___x_3442_ = lean_box(v___x_3395_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3442_);
v___x_3444_ = v___x_3427_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
else
{
uint8_t v___x_3446_; uint8_t v___x_3447_; uint8_t v___x_3448_; lean_object* v___x_3449_; uint64_t v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_del_object(v___x_3427_);
v___x_3446_ = 1;
v___x_3447_ = 0;
v___x_3448_ = 2;
v___x_3449_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3449_, 0, v___x_3395_);
lean_ctor_set_uint8(v___x_3449_, 1, v___x_3395_);
lean_ctor_set_uint8(v___x_3449_, 2, v___x_3395_);
lean_ctor_set_uint8(v___x_3449_, 3, v___x_3395_);
lean_ctor_set_uint8(v___x_3449_, 4, v___x_3395_);
lean_ctor_set_uint8(v___x_3449_, 5, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 6, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 7, v___x_3395_);
lean_ctor_set_uint8(v___x_3449_, 8, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 9, v___x_3446_);
lean_ctor_set_uint8(v___x_3449_, 10, v___x_3447_);
lean_ctor_set_uint8(v___x_3449_, 11, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 12, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 13, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 14, v___x_3448_);
lean_ctor_set_uint8(v___x_3449_, 15, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 16, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 17, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3449_, 18, v_hasTrace_3088_);
v___x_3450_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3449_);
v___x_3451_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set_uint64(v___x_3451_, sizeof(void*)*1, v___x_3450_);
v___x_3452_ = lean_box(1);
v___x_3453_ = lean_unsigned_to_nat(0u);
v___x_3454_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3455_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3456_ = lean_box(0);
v___x_3457_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3457_, 0, v___x_3451_);
lean_ctor_set(v___x_3457_, 1, v___x_3452_);
lean_ctor_set(v___x_3457_, 2, v___x_3454_);
lean_ctor_set(v___x_3457_, 3, v___x_3455_);
lean_ctor_set(v___x_3457_, 4, v___x_3456_);
lean_ctor_set(v___x_3457_, 5, v___x_3453_);
lean_ctor_set(v___x_3457_, 6, v___x_3456_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*7, v___x_3395_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*7 + 1, v___x_3395_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*7 + 2, v___x_3395_);
lean_ctor_set_uint8(v___x_3457_, sizeof(void*)*7 + 3, v_hasTrace_3088_);
v___x_3458_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3459_ = lean_st_mk_ref(v___x_3458_);
v___x_3460_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3429_, v_hasTrace_3088_, v___x_3457_, v___x_3459_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___x_3457_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref(v___x_3460_);
v___x_3462_ = lean_st_ref_get(v___x_3459_);
lean_dec(v___x_3459_);
lean_dec(v___x_3462_);
v_a_3410_ = v_a_3461_;
goto v___jp_3409_;
}
else
{
lean_dec(v___x_3459_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3463_; 
v_a_3463_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3460_);
v_a_3410_ = v_a_3463_;
goto v___jp_3409_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
v_a_3464_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3460_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3460_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
else
{
uint8_t v___x_3472_; uint8_t v___x_3473_; uint8_t v___x_3474_; lean_object* v___x_3475_; uint64_t v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_dec(v_snd_3430_);
lean_del_object(v___x_3427_);
v___x_3472_ = 1;
v___x_3473_ = 0;
v___x_3474_ = 2;
v___x_3475_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3475_, 0, v___x_3395_);
lean_ctor_set_uint8(v___x_3475_, 1, v___x_3395_);
lean_ctor_set_uint8(v___x_3475_, 2, v___x_3395_);
lean_ctor_set_uint8(v___x_3475_, 3, v___x_3395_);
lean_ctor_set_uint8(v___x_3475_, 4, v___x_3395_);
lean_ctor_set_uint8(v___x_3475_, 5, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 6, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 7, v___x_3395_);
lean_ctor_set_uint8(v___x_3475_, 8, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 9, v___x_3472_);
lean_ctor_set_uint8(v___x_3475_, 10, v___x_3473_);
lean_ctor_set_uint8(v___x_3475_, 11, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 12, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 13, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 14, v___x_3474_);
lean_ctor_set_uint8(v___x_3475_, 15, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 16, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 17, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3475_, 18, v_hasTrace_3088_);
v___x_3476_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3475_);
v___x_3477_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set_uint64(v___x_3477_, sizeof(void*)*1, v___x_3476_);
v___x_3478_ = lean_box(1);
v___x_3479_ = lean_unsigned_to_nat(0u);
v___x_3480_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3481_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3482_ = lean_box(0);
v___x_3483_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3483_, 0, v___x_3477_);
lean_ctor_set(v___x_3483_, 1, v___x_3478_);
lean_ctor_set(v___x_3483_, 2, v___x_3480_);
lean_ctor_set(v___x_3483_, 3, v___x_3481_);
lean_ctor_set(v___x_3483_, 4, v___x_3482_);
lean_ctor_set(v___x_3483_, 5, v___x_3479_);
lean_ctor_set(v___x_3483_, 6, v___x_3482_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7, v___x_3395_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 1, v___x_3395_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 2, v___x_3395_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 3, v_hasTrace_3088_);
v___x_3484_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3485_ = lean_st_mk_ref(v___x_3484_);
v___x_3486_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3429_, v___x_3483_, v___x_3485_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___x_3483_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref(v___x_3486_);
v___x_3488_ = lean_st_ref_get(v___x_3485_);
lean_dec(v___x_3485_);
lean_dec(v___x_3488_);
v_a_3397_ = v_a_3487_;
goto v___jp_3396_;
}
else
{
lean_dec(v___x_3485_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3489_; 
v_a_3489_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v___x_3486_);
v_a_3397_ = v_a_3489_;
goto v___jp_3396_;
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_a_3490_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3486_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3486_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
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
lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_dec(v___x_3424_);
lean_dec(v_name_3083_);
v___x_3499_ = lean_box(v___x_3395_);
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
return v___x_3500_;
}
}
else
{
goto v___jp_3278_;
}
v___jp_3396_:
{
if (lean_obj_tag(v_a_3397_) == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_box(v___x_3395_);
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
else
{
lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3407_; 
v_isSharedCheck_3407_ = !lean_is_exclusive(v_a_3397_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v_a_3397_, 0);
lean_dec(v_unused_3408_);
v___x_3401_ = v_a_3397_;
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
else
{
lean_dec(v_a_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = lean_box(v_hasTrace_3088_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3403_);
v___x_3405_ = v___x_3401_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
v___jp_3409_:
{
if (lean_obj_tag(v_a_3410_) == 0)
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = lean_box(v___x_3395_);
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
return v___x_3412_;
}
else
{
lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_isSharedCheck_3420_ = !lean_is_exclusive(v_a_3410_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; 
v_unused_3421_ = lean_ctor_get(v_a_3410_, 0);
lean_dec(v_unused_3421_);
v___x_3414_ = v_a_3410_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_dec(v_a_3410_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = lean_box(v_hasTrace_3088_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set_tag(v___x_3414_, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
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
else
{
goto v___jp_3278_;
}
v___jp_3200_:
{
lean_object* v___x_3204_; double v___x_3205_; double v___x_3206_; double v___x_3207_; double v___x_3208_; double v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3204_ = lean_io_mono_nanos_now();
v___x_3205_ = lean_float_of_nat(v___y_3201_);
v___x_3206_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3207_ = lean_float_div(v___x_3205_, v___x_3206_);
v___x_3208_ = lean_float_of_nat(v___x_3204_);
v___x_3209_ = lean_float_div(v___x_3208_, v___x_3206_);
v___x_3210_ = lean_box_float(v___x_3207_);
v___x_3211_ = lean_box_float(v___x_3209_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v_a_3203_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3196_, v_hasTrace_3088_, v___x_3197_, v_options_3087_, v___x_3199_, v___y_3202_, v___f_3195_, v___x_3213_, v___y_3084_, v___y_3085_);
return v___x_3214_;
}
v___jp_3215_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_box(v_a_3218_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
v___y_3201_ = v___y_3216_;
v___y_3202_ = v___y_3217_;
v_a_3203_ = v___x_3220_;
goto v___jp_3200_;
}
v___jp_3221_:
{
if (lean_obj_tag(v_a_3225_) == 0)
{
v___y_3216_ = v___y_3222_;
v___y_3217_ = v___y_3223_;
v_a_3218_ = v___y_3224_;
goto v___jp_3215_;
}
else
{
lean_dec_ref(v_a_3225_);
v___y_3216_ = v___y_3222_;
v___y_3217_ = v___y_3223_;
v_a_3218_ = v_hasTrace_3088_;
goto v___jp_3215_;
}
}
v___jp_3226_:
{
if (lean_obj_tag(v_a_3230_) == 0)
{
v___y_3216_ = v___y_3227_;
v___y_3217_ = v___y_3228_;
v_a_3218_ = v___y_3229_;
goto v___jp_3215_;
}
else
{
lean_dec_ref(v_a_3230_);
v___y_3216_ = v___y_3227_;
v___y_3217_ = v___y_3228_;
v_a_3218_ = v_hasTrace_3088_;
goto v___jp_3215_;
}
}
v___jp_3231_:
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3235_, 0, v_a_3234_);
v___y_3201_ = v___y_3232_;
v___y_3202_ = v___y_3233_;
v_a_3203_ = v___x_3235_;
goto v___jp_3200_;
}
v___jp_3236_:
{
lean_object* v___x_3240_; double v___x_3241_; double v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3240_ = lean_io_get_num_heartbeats();
v___x_3241_ = lean_float_of_nat(v___y_3238_);
v___x_3242_ = lean_float_of_nat(v___x_3240_);
v___x_3243_ = lean_box_float(v___x_3241_);
v___x_3244_ = lean_box_float(v___x_3242_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_a_3239_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3196_, v_hasTrace_3088_, v___x_3197_, v_options_3087_, v___x_3199_, v___y_3237_, v___f_3195_, v___x_3246_, v___y_3084_, v___y_3085_);
return v___x_3247_;
}
v___jp_3248_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = lean_box(v_a_3251_);
v___x_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
v___y_3237_ = v___y_3249_;
v___y_3238_ = v___y_3250_;
v_a_3239_ = v___x_3253_;
goto v___jp_3236_;
}
v___jp_3254_:
{
if (lean_obj_tag(v_a_3259_) == 0)
{
v___y_3249_ = v___y_3257_;
v___y_3250_ = v___y_3258_;
v_a_3251_ = v___y_3255_;
goto v___jp_3248_;
}
else
{
lean_dec_ref(v_a_3259_);
v___y_3249_ = v___y_3257_;
v___y_3250_ = v___y_3258_;
v_a_3251_ = v___y_3256_;
goto v___jp_3248_;
}
}
v___jp_3260_:
{
if (lean_obj_tag(v_a_3264_) == 0)
{
uint8_t v___x_3265_; 
v___x_3265_ = 0;
v___y_3249_ = v___y_3262_;
v___y_3250_ = v___y_3263_;
v_a_3251_ = v___x_3265_;
goto v___jp_3248_;
}
else
{
lean_dec_ref(v_a_3264_);
v___y_3249_ = v___y_3262_;
v___y_3250_ = v___y_3263_;
v_a_3251_ = v___y_3261_;
goto v___jp_3248_;
}
}
v___jp_3266_:
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v_a_3269_);
v___y_3237_ = v___y_3267_;
v___y_3238_ = v___y_3268_;
v_a_3239_ = v___x_3270_;
goto v___jp_3236_;
}
v___jp_3271_:
{
if (lean_obj_tag(v___y_3274_) == 0)
{
lean_object* v_a_3275_; uint8_t v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___y_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___y_3274_);
v___x_3276_ = lean_unbox(v_a_3275_);
lean_dec(v_a_3275_);
v___y_3249_ = v___y_3272_;
v___y_3250_ = v___y_3273_;
v_a_3251_ = v___x_3276_;
goto v___jp_3248_;
}
else
{
lean_object* v_a_3277_; 
v_a_3277_ = lean_ctor_get(v___y_3274_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___y_3274_);
v___y_3267_ = v___y_3272_;
v___y_3268_ = v___y_3273_;
v_a_3269_ = v_a_3277_;
goto v___jp_3266_;
}
}
v___jp_3278_:
{
lean_object* v___x_3279_; lean_object* v_a_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3279_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3085_);
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref(v___x_3279_);
v___x_3281_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3282_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3087_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v_env_3285_; lean_object* v___x_3286_; 
lean_dec_ref(v___f_3082_);
v___x_3283_ = lean_io_mono_nanos_now();
v___x_3284_ = lean_st_ref_get(v___y_3085_);
v_env_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc_ref(v_env_3285_);
lean_dec(v___x_3284_);
lean_inc(v_name_3083_);
v___x_3286_ = l_Lean_Meta_declFromEqLikeName(v_env_3285_, v_name_3083_);
if (lean_obj_tag(v___x_3286_) == 1)
{
lean_object* v_val_3287_; lean_object* v_fst_3288_; lean_object* v_snd_3289_; lean_object* v___x_3290_; lean_object* v_env_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v_val_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_val_3287_);
lean_dec_ref(v___x_3286_);
v_fst_3288_ = lean_ctor_get(v_val_3287_, 0);
lean_inc_n(v_fst_3288_, 2);
v_snd_3289_ = lean_ctor_get(v_val_3287_, 1);
lean_inc_n(v_snd_3289_, 2);
lean_dec(v_val_3287_);
v___x_3290_ = lean_st_ref_get(v___y_3085_);
v_env_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc_ref(v_env_3291_);
lean_dec(v___x_3290_);
v___x_3292_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3291_, v_fst_3288_, v_snd_3289_);
v___x_3293_ = lean_name_eq(v_name_3083_, v___x_3292_);
lean_dec(v___x_3292_);
lean_dec(v_name_3083_);
if (v___x_3293_ == 0)
{
lean_dec(v_snd_3289_);
lean_dec(v_fst_3288_);
v___y_3216_ = v___x_3283_;
v___y_3217_ = v_a_3280_;
v_a_3218_ = v___x_3282_;
goto v___jp_3215_;
}
else
{
uint8_t v___x_3294_; 
lean_inc(v_snd_3289_);
v___x_3294_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3289_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3296_ = lean_string_dec_eq(v_snd_3289_, v___x_3295_);
lean_dec(v_snd_3289_);
if (v___x_3296_ == 0)
{
lean_dec(v_fst_3288_);
v___y_3216_ = v___x_3283_;
v___y_3217_ = v_a_3280_;
v_a_3218_ = v___x_3282_;
goto v___jp_3215_;
}
else
{
uint8_t v___x_3297_; uint8_t v___x_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; uint64_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3297_ = 1;
v___x_3298_ = 0;
v___x_3299_ = 2;
v___x_3300_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3300_, 0, v___x_3282_);
lean_ctor_set_uint8(v___x_3300_, 1, v___x_3282_);
lean_ctor_set_uint8(v___x_3300_, 2, v___x_3282_);
lean_ctor_set_uint8(v___x_3300_, 3, v___x_3282_);
lean_ctor_set_uint8(v___x_3300_, 4, v___x_3282_);
lean_ctor_set_uint8(v___x_3300_, 5, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 6, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 7, v___x_3282_);
lean_ctor_set_uint8(v___x_3300_, 8, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 9, v___x_3297_);
lean_ctor_set_uint8(v___x_3300_, 10, v___x_3298_);
lean_ctor_set_uint8(v___x_3300_, 11, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 12, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 13, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 14, v___x_3299_);
lean_ctor_set_uint8(v___x_3300_, 15, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 16, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 17, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3300_, 18, v_hasTrace_3088_);
v___x_3301_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3300_);
v___x_3302_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set_uint64(v___x_3302_, sizeof(void*)*1, v___x_3301_);
v___x_3303_ = lean_box(1);
v___x_3304_ = lean_unsigned_to_nat(0u);
v___x_3305_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3306_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3308_, 0, v___x_3302_);
lean_ctor_set(v___x_3308_, 1, v___x_3303_);
lean_ctor_set(v___x_3308_, 2, v___x_3305_);
lean_ctor_set(v___x_3308_, 3, v___x_3306_);
lean_ctor_set(v___x_3308_, 4, v___x_3307_);
lean_ctor_set(v___x_3308_, 5, v___x_3304_);
lean_ctor_set(v___x_3308_, 6, v___x_3307_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*7, v___x_3282_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*7 + 1, v___x_3282_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*7 + 2, v___x_3282_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*7 + 3, v_hasTrace_3088_);
v___x_3309_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3310_ = lean_st_mk_ref(v___x_3309_);
v___x_3311_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3288_, v_hasTrace_3088_, v___x_3308_, v___x_3310_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___x_3308_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = lean_st_ref_get(v___x_3310_);
lean_dec(v___x_3310_);
lean_dec(v___x_3313_);
v___y_3227_ = v___x_3283_;
v___y_3228_ = v_a_3280_;
v___y_3229_ = v___x_3282_;
v_a_3230_ = v_a_3312_;
goto v___jp_3226_;
}
else
{
lean_dec(v___x_3310_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3314_; 
v_a_3314_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3314_);
lean_dec_ref(v___x_3311_);
v___y_3227_ = v___x_3283_;
v___y_3228_ = v_a_3280_;
v___y_3229_ = v___x_3282_;
v_a_3230_ = v_a_3314_;
goto v___jp_3226_;
}
else
{
lean_object* v_a_3315_; 
v_a_3315_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3311_);
v___y_3232_ = v___x_3283_;
v___y_3233_ = v_a_3280_;
v_a_3234_ = v_a_3315_;
goto v___jp_3231_;
}
}
}
}
else
{
uint8_t v___x_3316_; uint8_t v___x_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; uint64_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec(v_snd_3289_);
v___x_3316_ = 1;
v___x_3317_ = 0;
v___x_3318_ = 2;
v___x_3319_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3319_, 0, v___x_3282_);
lean_ctor_set_uint8(v___x_3319_, 1, v___x_3282_);
lean_ctor_set_uint8(v___x_3319_, 2, v___x_3282_);
lean_ctor_set_uint8(v___x_3319_, 3, v___x_3282_);
lean_ctor_set_uint8(v___x_3319_, 4, v___x_3282_);
lean_ctor_set_uint8(v___x_3319_, 5, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 6, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 7, v___x_3282_);
lean_ctor_set_uint8(v___x_3319_, 8, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 9, v___x_3316_);
lean_ctor_set_uint8(v___x_3319_, 10, v___x_3317_);
lean_ctor_set_uint8(v___x_3319_, 11, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 12, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 13, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 14, v___x_3318_);
lean_ctor_set_uint8(v___x_3319_, 15, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 16, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 17, v_hasTrace_3088_);
lean_ctor_set_uint8(v___x_3319_, 18, v_hasTrace_3088_);
v___x_3320_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3319_);
v___x_3321_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set_uint64(v___x_3321_, sizeof(void*)*1, v___x_3320_);
v___x_3322_ = lean_box(1);
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3324_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3327_, 0, v___x_3321_);
lean_ctor_set(v___x_3327_, 1, v___x_3322_);
lean_ctor_set(v___x_3327_, 2, v___x_3324_);
lean_ctor_set(v___x_3327_, 3, v___x_3325_);
lean_ctor_set(v___x_3327_, 4, v___x_3326_);
lean_ctor_set(v___x_3327_, 5, v___x_3323_);
lean_ctor_set(v___x_3327_, 6, v___x_3326_);
lean_ctor_set_uint8(v___x_3327_, sizeof(void*)*7, v___x_3282_);
lean_ctor_set_uint8(v___x_3327_, sizeof(void*)*7 + 1, v___x_3282_);
lean_ctor_set_uint8(v___x_3327_, sizeof(void*)*7 + 2, v___x_3282_);
lean_ctor_set_uint8(v___x_3327_, sizeof(void*)*7 + 3, v_hasTrace_3088_);
v___x_3328_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3329_ = lean_st_mk_ref(v___x_3328_);
v___x_3330_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3288_, v___x_3327_, v___x_3329_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___x_3327_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref(v___x_3330_);
v___x_3332_ = lean_st_ref_get(v___x_3329_);
lean_dec(v___x_3329_);
lean_dec(v___x_3332_);
v___y_3222_ = v___x_3283_;
v___y_3223_ = v_a_3280_;
v___y_3224_ = v___x_3282_;
v_a_3225_ = v_a_3331_;
goto v___jp_3221_;
}
else
{
lean_dec(v___x_3329_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3333_; 
v_a_3333_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3333_);
lean_dec_ref(v___x_3330_);
v___y_3222_ = v___x_3283_;
v___y_3223_ = v_a_3280_;
v___y_3224_ = v___x_3282_;
v_a_3225_ = v_a_3333_;
goto v___jp_3221_;
}
else
{
lean_object* v_a_3334_; 
v_a_3334_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3334_);
lean_dec_ref(v___x_3330_);
v___y_3232_ = v___x_3283_;
v___y_3233_ = v_a_3280_;
v_a_3234_ = v_a_3334_;
goto v___jp_3231_;
}
}
}
}
}
else
{
lean_dec(v___x_3286_);
lean_dec(v_name_3083_);
v___y_3216_ = v___x_3283_;
v___y_3217_ = v_a_3280_;
v_a_3218_ = v___x_3282_;
goto v___jp_3215_;
}
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v_env_3337_; lean_object* v___x_3338_; 
v___x_3335_ = lean_io_get_num_heartbeats();
v___x_3336_ = lean_st_ref_get(v___y_3085_);
v_env_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc_ref(v_env_3337_);
lean_dec(v___x_3336_);
lean_inc(v_name_3083_);
v___x_3338_ = l_Lean_Meta_declFromEqLikeName(v_env_3337_, v_name_3083_);
if (lean_obj_tag(v___x_3338_) == 1)
{
lean_object* v_val_3339_; lean_object* v_fst_3340_; lean_object* v_snd_3341_; lean_object* v___x_3342_; lean_object* v_env_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_val_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_val_3339_);
lean_dec_ref(v___x_3338_);
v_fst_3340_ = lean_ctor_get(v_val_3339_, 0);
lean_inc_n(v_fst_3340_, 2);
v_snd_3341_ = lean_ctor_get(v_val_3339_, 1);
lean_inc_n(v_snd_3341_, 2);
lean_dec(v_val_3339_);
v___x_3342_ = lean_st_ref_get(v___y_3085_);
v_env_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc_ref(v_env_3343_);
lean_dec(v___x_3342_);
v___x_3344_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3343_, v_fst_3340_, v_snd_3341_);
v___x_3345_ = lean_name_eq(v_name_3083_, v___x_3344_);
lean_dec(v___x_3344_);
lean_dec(v_name_3083_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec(v_snd_3341_);
lean_dec(v_fst_3340_);
v___x_3346_ = lean_box(0);
lean_inc(v___y_3085_);
lean_inc_ref(v___y_3084_);
v___x_3347_ = lean_apply_4(v___f_3082_, v___x_3346_, v___y_3084_, v___y_3085_, lean_box(0));
v___y_3272_ = v_a_3280_;
v___y_3273_ = v___x_3335_;
v___y_3274_ = v___x_3347_;
goto v___jp_3271_;
}
else
{
uint8_t v___x_3348_; 
lean_inc(v_snd_3341_);
v___x_3348_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3341_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3350_ = lean_string_dec_eq(v_snd_3341_, v___x_3349_);
lean_dec(v_snd_3341_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_dec(v_fst_3340_);
v___x_3351_ = lean_box(0);
lean_inc(v___y_3085_);
lean_inc_ref(v___y_3084_);
v___x_3352_ = lean_apply_4(v___f_3082_, v___x_3351_, v___y_3084_, v___y_3085_, lean_box(0));
v___y_3272_ = v_a_3280_;
v___y_3273_ = v___x_3335_;
v___y_3274_ = v___x_3352_;
goto v___jp_3271_;
}
else
{
uint8_t v___x_3353_; uint8_t v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; uint64_t v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec_ref(v___f_3082_);
v___x_3353_ = 1;
v___x_3354_ = 0;
v___x_3355_ = 2;
v___x_3356_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3356_, 0, v___x_3348_);
lean_ctor_set_uint8(v___x_3356_, 1, v___x_3348_);
lean_ctor_set_uint8(v___x_3356_, 2, v___x_3348_);
lean_ctor_set_uint8(v___x_3356_, 3, v___x_3348_);
lean_ctor_set_uint8(v___x_3356_, 4, v___x_3348_);
lean_ctor_set_uint8(v___x_3356_, 5, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 6, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 7, v___x_3348_);
lean_ctor_set_uint8(v___x_3356_, 8, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 9, v___x_3353_);
lean_ctor_set_uint8(v___x_3356_, 10, v___x_3354_);
lean_ctor_set_uint8(v___x_3356_, 11, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 12, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 13, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 14, v___x_3355_);
lean_ctor_set_uint8(v___x_3356_, 15, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 16, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 17, v___x_3282_);
lean_ctor_set_uint8(v___x_3356_, 18, v___x_3282_);
v___x_3357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set_uint64(v___x_3358_, sizeof(void*)*1, v___x_3357_);
v___x_3359_ = lean_box(1);
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3364_, 0, v___x_3358_);
lean_ctor_set(v___x_3364_, 1, v___x_3359_);
lean_ctor_set(v___x_3364_, 2, v___x_3361_);
lean_ctor_set(v___x_3364_, 3, v___x_3362_);
lean_ctor_set(v___x_3364_, 4, v___x_3363_);
lean_ctor_set(v___x_3364_, 5, v___x_3360_);
lean_ctor_set(v___x_3364_, 6, v___x_3363_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7, v___x_3348_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 1, v___x_3348_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 2, v___x_3348_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 3, v___x_3282_);
v___x_3365_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3366_ = lean_st_mk_ref(v___x_3365_);
v___x_3367_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3340_, v___x_3282_, v___x_3364_, v___x_3366_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___x_3364_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3369_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref(v___x_3367_);
v___x_3369_ = lean_st_ref_get(v___x_3366_);
lean_dec(v___x_3366_);
lean_dec(v___x_3369_);
v___y_3255_ = v___x_3348_;
v___y_3256_ = v___x_3282_;
v___y_3257_ = v_a_3280_;
v___y_3258_ = v___x_3335_;
v_a_3259_ = v_a_3368_;
goto v___jp_3254_;
}
else
{
lean_dec(v___x_3366_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3370_; 
v_a_3370_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3370_);
lean_dec_ref(v___x_3367_);
v___y_3255_ = v___x_3348_;
v___y_3256_ = v___x_3282_;
v___y_3257_ = v_a_3280_;
v___y_3258_ = v___x_3335_;
v_a_3259_ = v_a_3370_;
goto v___jp_3254_;
}
else
{
lean_object* v_a_3371_; 
v_a_3371_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3371_);
lean_dec_ref(v___x_3367_);
v___y_3267_ = v_a_3280_;
v___y_3268_ = v___x_3335_;
v_a_3269_ = v_a_3371_;
goto v___jp_3266_;
}
}
}
}
else
{
uint8_t v___x_3372_; uint8_t v___x_3373_; uint8_t v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; uint64_t v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec(v_snd_3341_);
lean_dec_ref(v___f_3082_);
v___x_3372_ = 0;
v___x_3373_ = 1;
v___x_3374_ = 0;
v___x_3375_ = 2;
v___x_3376_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3376_, 0, v___x_3372_);
lean_ctor_set_uint8(v___x_3376_, 1, v___x_3372_);
lean_ctor_set_uint8(v___x_3376_, 2, v___x_3372_);
lean_ctor_set_uint8(v___x_3376_, 3, v___x_3372_);
lean_ctor_set_uint8(v___x_3376_, 4, v___x_3372_);
lean_ctor_set_uint8(v___x_3376_, 5, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 6, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 7, v___x_3372_);
lean_ctor_set_uint8(v___x_3376_, 8, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 9, v___x_3373_);
lean_ctor_set_uint8(v___x_3376_, 10, v___x_3374_);
lean_ctor_set_uint8(v___x_3376_, 11, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 12, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 13, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 14, v___x_3375_);
lean_ctor_set_uint8(v___x_3376_, 15, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 16, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 17, v___x_3282_);
lean_ctor_set_uint8(v___x_3376_, 18, v___x_3282_);
v___x_3377_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3376_);
v___x_3378_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set_uint64(v___x_3378_, sizeof(void*)*1, v___x_3377_);
v___x_3379_ = lean_box(1);
v___x_3380_ = lean_unsigned_to_nat(0u);
v___x_3381_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3382_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3383_ = lean_box(0);
v___x_3384_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3384_, 0, v___x_3378_);
lean_ctor_set(v___x_3384_, 1, v___x_3379_);
lean_ctor_set(v___x_3384_, 2, v___x_3381_);
lean_ctor_set(v___x_3384_, 3, v___x_3382_);
lean_ctor_set(v___x_3384_, 4, v___x_3383_);
lean_ctor_set(v___x_3384_, 5, v___x_3380_);
lean_ctor_set(v___x_3384_, 6, v___x_3383_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*7, v___x_3372_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*7 + 1, v___x_3372_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*7 + 2, v___x_3372_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*7 + 3, v___x_3282_);
v___x_3385_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3386_ = lean_st_mk_ref(v___x_3385_);
v___x_3387_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3340_, v___x_3384_, v___x_3386_, v___y_3084_, v___y_3085_);
lean_dec_ref(v___x_3384_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref(v___x_3387_);
v___x_3389_ = lean_st_ref_get(v___x_3386_);
lean_dec(v___x_3386_);
lean_dec(v___x_3389_);
v___y_3261_ = v___x_3282_;
v___y_3262_ = v_a_3280_;
v___y_3263_ = v___x_3335_;
v_a_3264_ = v_a_3388_;
goto v___jp_3260_;
}
else
{
lean_dec(v___x_3386_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3390_; 
v_a_3390_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3390_);
lean_dec_ref(v___x_3387_);
v___y_3261_ = v___x_3282_;
v___y_3262_ = v_a_3280_;
v___y_3263_ = v___x_3335_;
v_a_3264_ = v_a_3390_;
goto v___jp_3260_;
}
else
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3391_);
lean_dec_ref(v___x_3387_);
v___y_3267_ = v_a_3280_;
v___y_3268_ = v___x_3335_;
v_a_3269_ = v_a_3391_;
goto v___jp_3266_;
}
}
}
}
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_dec(v___x_3338_);
lean_dec(v_name_3083_);
v___x_3392_ = lean_box(0);
lean_inc(v___y_3085_);
lean_inc_ref(v___y_3084_);
v___x_3393_ = lean_apply_4(v___f_3082_, v___x_3392_, v___y_3084_, v___y_3085_, lean_box(0));
v___y_3272_ = v_a_3280_;
v___y_3273_ = v___x_3335_;
v___y_3274_ = v___x_3393_;
goto v___jp_3271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3501_, lean_object* v_name_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3501_, v_name_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_unsigned_to_nat(3137104340u);
v___x_3551_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3552_ = l_Lean_Name_num___override(v___x_3551_, v___x_3550_);
return v___x_3552_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3555_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3556_ = l_Lean_Name_str___override(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3560_ = l_Lean_Name_str___override(v___x_3559_, v___x_3558_);
return v___x_3560_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = lean_unsigned_to_nat(2u);
v___x_3562_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3563_ = l_Lean_Name_num___override(v___x_3562_, v___x_3561_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3565_; lean_object* v___x_3566_; 
v___f_3565_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3566_ = l_Lean_registerReservedNameAction(v___f_3565_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v___x_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec_ref(v___x_3566_);
v___x_3567_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3568_ = 0;
v___x_3569_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3570_ = l_Lean_registerTraceClass(v___x_3567_, v___x_3568_, v___x_3569_);
return v___x_3570_;
}
else
{
return v___x_3566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b1_3573_, lean_object* v_x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_3574_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_00_u03b1_3579_, lean_object* v_x_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b1_3579_, v_x_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
return v_res_3584_;
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
res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_eqnOptionsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_eqnOptionsExt);
lean_dec_ref(res);
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
