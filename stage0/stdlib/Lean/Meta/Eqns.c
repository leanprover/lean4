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
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_backward_defeqAttrib_useBackward;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Eqns reserved name action for "};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ReservedNameAction"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 245, 189, 90, 36, 141, 82, 229)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Eqns"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 217, 145, 26, 133, 108, 104, 10)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(27, 2, 5, 79, 97, 142, 74, 217)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 112, 146, 108, 241, 250, 100, 162)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 0, 196, 176, 89, 93, 16, 10)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 31, 160, 103, 40, 58, 110, 116)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 147, 153, 14, 107, 3, 39, 172)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 114, 185, 94, 205, 199, 191, 156)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 255, 177, 29, 188, 255, 188, 249)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 48, 196, 25, 136, 122, 168, 47)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_92_ = l_Lean_backward_defeqAttrib_useBackward;
v___x_93_ = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
v___x_94_ = l_Lean_Meta_backward_eqns_nonrecursive;
v___x_95_ = lean_unsigned_to_nat(3u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_array_push(v___x_96_, v___x_94_);
v___x_98_ = lean_array_push(v___x_97_, v___x_93_);
v___x_99_ = lean_array_push(v___x_98_, v___x_92_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions(void){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lean_Meta_eqnAffectingOptions___closed__0, &l_Lean_Meta_eqnAffectingOptions___closed__0_once, _init_l_Lean_Meta_eqnAffectingOptions___closed__0);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(lean_object* v_env_101_, lean_object* v_as_102_, size_t v_i_103_, size_t v_stop_104_, lean_object* v_b_105_){
_start:
{
lean_object* v___y_107_; uint8_t v___x_111_; 
v___x_111_ = lean_usize_dec_eq(v_i_103_, v_stop_104_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v_fst_113_; uint8_t v___x_114_; 
v___x_112_ = lean_array_uget_borrowed(v_as_102_, v_i_103_);
v_fst_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_fst_113_);
lean_inc_ref(v_env_101_);
v___x_114_ = l_Lean_Environment_contains(v_env_101_, v_fst_113_, v___x_111_);
if (v___x_114_ == 0)
{
v___y_107_ = v_b_105_;
goto v___jp_106_;
}
else
{
lean_object* v___x_115_; 
lean_inc(v___x_112_);
v___x_115_ = lean_array_push(v_b_105_, v___x_112_);
v___y_107_ = v___x_115_;
goto v___jp_106_;
}
}
else
{
lean_dec_ref(v_env_101_);
return v_b_105_;
}
v___jp_106_:
{
size_t v___x_108_; size_t v___x_109_; 
v___x_108_ = ((size_t)1ULL);
v___x_109_ = lean_usize_add(v_i_103_, v___x_108_);
v_i_103_ = v___x_109_;
v_b_105_ = v___y_107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_116_, lean_object* v_as_117_, lean_object* v_i_118_, lean_object* v_stop_119_, lean_object* v_b_120_){
_start:
{
size_t v_i_boxed_121_; size_t v_stop_boxed_122_; lean_object* v_res_123_; 
v_i_boxed_121_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_stop_boxed_122_ = lean_unbox_usize(v_stop_119_);
lean_dec(v_stop_119_);
v_res_123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_116_, v_as_117_, v_i_boxed_121_, v_stop_boxed_122_, v_b_120_);
lean_dec_ref(v_as_117_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v_k_126_; lean_object* v_v_127_; lean_object* v_l_128_; lean_object* v_r_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_k_126_ = lean_ctor_get(v_x_125_, 1);
v_v_127_ = lean_ctor_get(v_x_125_, 2);
v_l_128_ = lean_ctor_get(v_x_125_, 3);
v_r_129_ = lean_ctor_get(v_x_125_, 4);
v___x_130_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_124_, v_l_128_);
lean_inc(v_v_127_);
lean_inc(v_k_126_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_k_126_);
lean_ctor_set(v___x_131_, 1, v_v_127_);
v___x_132_ = lean_array_push(v___x_130_, v___x_131_);
v_init_124_ = v___x_132_;
v_x_125_ = v_r_129_;
goto _start;
}
else
{
return v_init_124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_134_, lean_object* v_x_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_134_, v_x_135_);
lean_dec(v_x_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(lean_object* v_env_143_, lean_object* v_s_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_147_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v___x_146_, v_s_144_);
v___x_148_ = lean_array_get_size(v___x_147_);
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_150_ = lean_nat_dec_lt(v___x_145_, v___x_148_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec_ref(v___x_147_);
lean_dec_ref(v_env_143_);
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
return v___x_151_;
}
else
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_le(v___x_148_, v___x_148_);
if (v___x_152_ == 0)
{
if (v___x_150_ == 0)
{
lean_object* v___x_153_; 
lean_dec_ref(v___x_147_);
lean_dec_ref(v_env_143_);
v___x_153_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
return v___x_153_;
}
else
{
size_t v___x_154_; size_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = ((size_t)0ULL);
v___x_155_ = lean_usize_of_nat(v___x_148_);
v___x_156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_143_, v___x_147_, v___x_154_, v___x_155_, v___x_149_);
lean_dec_ref(v___x_147_);
lean_inc_ref_n(v___x_156_, 2);
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
return v___x_157_;
}
}
else
{
size_t v___x_158_; size_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = ((size_t)0ULL);
v___x_159_ = lean_usize_of_nat(v___x_148_);
v___x_160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_143_, v___x_147_, v___x_158_, v___x_159_, v___x_149_);
lean_dec_ref(v___x_147_);
lean_inc_ref_n(v___x_160_, 2);
v___x_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
lean_ctor_set(v___x_161_, 2, v___x_160_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_env_162_, lean_object* v_s_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(v_env_162_, v_s_163_);
lean_dec(v_s_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___f_172_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_173_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_));
v___x_174_ = lean_box(1);
v___x_175_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_173_, v___x_174_, v___f_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(lean_object* v_init_178_, lean_object* v_t_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_178_, v_t_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_181_, lean_object* v_t_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(v_init_181_, v_t_182_);
lean_dec(v_t_182_);
return v_res_183_;
}
}
static lean_object* _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_191_ = lean_string_utf8_byte_size(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* v_s_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_193_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_194_ = lean_string_utf8_byte_size(v_s_192_);
v___x_195_ = lean_obj_once(&l_Lean_Meta_isEqnReservedNameSuffix___closed__0, &l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0);
v___x_196_ = lean_nat_dec_le(v___x_195_, v___x_194_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_s_192_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_string_memcmp(v_s_192_, v___x_193_, v___x_197_, v___x_197_, v___x_195_);
if (v___x_198_ == 0)
{
lean_dec_ref(v_s_192_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_199_ = lean_unsigned_to_nat(3u);
lean_inc_ref(v_s_192_);
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v_s_192_);
lean_ctor_set(v___x_200_, 1, v___x_197_);
lean_ctor_set(v___x_200_, 2, v___x_194_);
v___x_201_ = l_String_Slice_Pos_nextn(v___x_200_, v___x_197_, v___x_199_);
lean_dec_ref_known(v___x_200_, 3);
v___x_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_202_, 0, v_s_192_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
lean_ctor_set(v___x_202_, 2, v___x_194_);
v___x_203_ = l_String_Slice_isNat(v___x_202_);
lean_dec_ref_known(v___x_202_, 3);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* v_s_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* v_s_211_){
_start:
{
uint8_t v___y_213_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_216_ = lean_string_dec_eq(v_s_211_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_218_ = lean_string_dec_eq(v_s_211_, v___x_217_);
v___y_213_ = v___x_218_;
goto v___jp_212_;
}
else
{
v___y_213_ = v___x_216_;
goto v___jp_212_;
}
v___jp_212_:
{
if (v___y_213_ == 0)
{
uint8_t v___x_214_; 
v___x_214_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_211_);
return v___x_214_;
}
else
{
lean_dec_ref(v_s_211_);
return v___y_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* v_s_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Lean_Meta_isEqnLikeSuffix(v_s_219_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_225_, lean_object* v_env_226_, lean_object* v_as_x27_227_, lean_object* v_b_228_){
_start:
{
if (lean_obj_tag(v_as_x27_227_) == 0)
{
lean_dec_ref(v_env_226_);
lean_dec_ref(v_str_225_);
lean_inc_ref(v_b_228_);
return v_b_228_;
}
else
{
lean_object* v_head_229_; lean_object* v_tail_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___y_234_; uint8_t v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_head_229_ = lean_ctor_get(v_as_x27_227_, 0);
v_tail_230_ = lean_ctor_get(v_as_x27_227_, 1);
v___x_231_ = lean_box(0);
v___x_232_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_240_ = 0;
lean_inc_ref(v_env_226_);
v___x_241_ = l_Lean_Environment_setExporting(v_env_226_, v___x_240_);
lean_inc(v_head_229_);
v___x_242_ = l_Lean_Environment_isSafeDefinition(v___x_241_, v_head_229_);
if (v___x_242_ == 0)
{
v___y_234_ = v___x_242_;
goto v___jp_233_;
}
else
{
uint8_t v___x_243_; uint8_t v___x_244_; 
lean_inc(v_head_229_);
lean_inc_ref(v_env_226_);
v___x_243_ = l_Lean_Meta_isMatcherCore(v_env_226_, v_head_229_);
v___x_244_ = lean_bool_not(v___x_243_);
v___y_234_ = v___x_244_;
goto v___jp_233_;
}
v___jp_233_:
{
if (v___y_234_ == 0)
{
v_as_x27_227_ = v_tail_230_;
v_b_228_ = v___x_232_;
goto _start;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_env_226_);
lean_inc(v_head_229_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_head_229_);
lean_ctor_set(v___x_236_, 1, v_str_225_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_231_);
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_245_, lean_object* v_env_246_, lean_object* v_as_x27_247_, lean_object* v_b_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_245_, v_env_246_, v_as_x27_247_, v_b_248_);
lean_dec_ref(v_b_248_);
lean_dec(v_as_x27_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_250_, lean_object* v_name_251_){
_start:
{
if (lean_obj_tag(v_name_251_) == 1)
{
lean_object* v_pre_252_; lean_object* v_str_253_; uint8_t v___x_254_; 
v_pre_252_ = lean_ctor_get(v_name_251_, 0);
lean_inc(v_pre_252_);
v_str_253_ = lean_ctor_get(v_name_251_, 1);
lean_inc_ref_n(v_str_253_, 2);
lean_dec_ref_known(v_name_251_, 2);
v___x_254_ = l_Lean_Meta_isEqnLikeSuffix(v_str_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec_ref(v_str_253_);
lean_dec(v_pre_252_);
lean_dec_ref(v_env_250_);
v___x_255_ = lean_box(0);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_fst_263_; 
lean_inc(v_pre_252_);
v___x_256_ = l_Lean_privateToUserName(v_pre_252_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v_pre_252_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_box(0);
v___x_261_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_262_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_253_, v_env_250_, v___x_259_, v___x_261_);
lean_dec_ref_known(v___x_259_, 2);
v_fst_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_fst_263_);
lean_dec_ref(v___x_262_);
if (lean_obj_tag(v_fst_263_) == 0)
{
return v___x_260_;
}
else
{
lean_object* v_val_264_; 
v_val_264_ = lean_ctor_get(v_fst_263_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v_fst_263_, 1);
return v_val_264_;
}
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v_name_251_);
lean_dec_ref(v_env_250_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_266_, lean_object* v_env_267_, lean_object* v_as_268_, lean_object* v_as_x27_269_, lean_object* v_b_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_266_, v_env_267_, v_as_x27_269_, v_b_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_273_, lean_object* v_env_274_, lean_object* v_as_275_, lean_object* v_as_x27_276_, lean_object* v_b_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_273_, v_env_274_, v_as_275_, v_as_x27_276_, v_b_277_, v_a_278_);
lean_dec_ref(v_b_277_);
lean_dec(v_as_x27_276_);
lean_dec(v_as_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_280_, lean_object* v_declName_281_, lean_object* v_suffix_282_){
_start:
{
uint8_t v_isExposed_283_; lean_object* v_name_284_; 
lean_inc(v_declName_281_);
lean_inc_ref(v_env_280_);
v_isExposed_283_ = l_Lean_Environment_hasExposedBody(v_env_280_, v_declName_281_);
v_name_284_ = l_Lean_Name_str___override(v_declName_281_, v_suffix_282_);
if (v_isExposed_283_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_mkPrivateName(v_env_280_, v_name_284_);
lean_dec_ref(v_env_280_);
return v___x_285_;
}
else
{
lean_dec_ref(v_env_280_);
return v_name_284_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_286_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
lean_ctor_set(v___x_291_, 2, v___x_290_);
lean_ctor_set(v___x_291_, 3, v___x_290_);
lean_ctor_set(v___x_291_, 4, v___x_289_);
lean_ctor_set(v___x_291_, 5, v___x_289_);
lean_ctor_set(v___x_291_, 6, v___x_289_);
lean_ctor_set(v___x_291_, 7, v___x_289_);
lean_ctor_set(v___x_291_, 8, v___x_289_);
lean_ctor_set(v___x_291_, 9, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(32u);
v___x_293_ = lean_mk_empty_array_with_capacity(v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_295_ = ((size_t)5ULL);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_unsigned_to_nat(32u);
v___x_298_ = lean_mk_empty_array_with_capacity(v___x_297_);
v___x_299_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_300_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_296_);
lean_ctor_set(v___x_300_, 3, v___x_296_);
lean_ctor_set_usize(v___x_300_, 4, v___x_295_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = lean_box(1);
v___x_302_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_303_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_301_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_env_310_; lean_object* v_options_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_309_ = lean_st_ref_get(v___y_307_);
v_env_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_env_310_);
lean_dec(v___x_309_);
v_options_311_ = lean_ctor_get(v___y_306_, 2);
v___x_312_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_313_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_311_);
v___x_314_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_314_, 0, v_env_310_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_ctor_set(v___x_314_, 3, v_options_311_);
v___x_315_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_msgData_305_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_ref_326_; lean_object* v___x_327_; lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_ref_326_ = lean_ctor_get(v___y_323_, 5);
v___x_327_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_322_, v___y_323_, v___y_324_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
lean_inc(v_ref_326_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_ref_326_);
lean_ctor_set(v___x_332_, 1, v_a_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 1);
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_351_, lean_object* v_reservedName_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_356_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_357_ = 0;
v___x_358_ = l_Lean_MessageData_ofConstName(v_declName_351_, v___x_357_);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_356_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = 1;
v___x_363_ = l_Lean_MessageData_ofConstName(v_reservedName_352_, v___x_362_);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_361_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_366_, v___y_353_, v___y_354_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_368_, lean_object* v_reservedName_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_368_, v_reservedName_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_374_, lean_object* v_suffix_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; lean_object* v_env_380_; lean_object* v_reservedName_381_; uint8_t v___x_382_; uint8_t v___x_383_; 
v___x_379_ = lean_st_ref_get(v___y_377_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_env_380_);
lean_dec(v___x_379_);
lean_inc(v_declName_374_);
v_reservedName_381_ = l_Lean_Name_str___override(v_declName_374_, v_suffix_375_);
v___x_382_ = 1;
lean_inc(v_reservedName_381_);
v___x_383_ = l_Lean_Environment_contains(v_env_380_, v_reservedName_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_reservedName_381_);
lean_dec(v_declName_374_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_374_, v_reservedName_381_, v___y_376_, v___y_377_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_387_, lean_object* v_suffix_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_387_, v_suffix_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_393_);
v___x_398_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_393_, v___x_397_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_399_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_393_);
v___x_400_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_393_, v___x_399_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref_known(v___x_400_, 1);
v___x_401_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_402_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_393_, v___x_401_, v_a_394_, v_a_395_);
return v___x_402_;
}
else
{
lean_dec(v_declName_393_);
return v___x_400_;
}
}
else
{
lean_dec(v_declName_393_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_409_, v___y_410_, v___y_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_414_, lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_414_, v_msg_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_420_, lean_object* v_n_421_){
_start:
{
lean_object* v___x_422_; 
lean_inc(v_n_421_);
lean_inc_ref(v_env_420_);
v___x_422_ = l_Lean_Meta_declFromEqLikeName(v_env_420_, v_n_421_);
if (lean_obj_tag(v___x_422_) == 1)
{
lean_object* v_val_423_; lean_object* v_fst_424_; lean_object* v_snd_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_val_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v___x_422_, 1);
v_fst_424_ = lean_ctor_get(v_val_423_, 0);
lean_inc(v_fst_424_);
v_snd_425_ = lean_ctor_get(v_val_423_, 1);
lean_inc(v_snd_425_);
lean_dec(v_val_423_);
v___x_426_ = l_Lean_Meta_mkEqLikeNameFor(v_env_420_, v_fst_424_, v_snd_425_);
v___x_427_ = lean_name_eq(v_n_421_, v___x_426_);
lean_dec(v___x_426_);
lean_dec(v_n_421_);
return v___x_427_;
}
else
{
uint8_t v___x_428_; 
lean_dec(v___x_422_);
lean_dec(v_n_421_);
lean_dec_ref(v_env_420_);
v___x_428_ = 0;
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_429_, lean_object* v_n_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_429_, v_n_430_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_435_; lean_object* v___x_436_; 
v___f_435_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_436_ = l_Lean_registerReservedNamePredicate(v___f_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_st_mk_ref(v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_444_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_447_ = lean_mk_io_user_error(v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_initializing();
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_467_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_467_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_467_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_467_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
uint8_t v___x_455_; 
v___x_455_ = lean_unbox(v_a_451_);
lean_dec(v_a_451_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_458_; 
lean_dec_ref(v_f_448_);
v___x_456_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 1);
lean_ctor_set(v___x_453_, 0, v___x_456_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_460_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_461_ = lean_st_ref_take(v___x_460_);
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v_f_448_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = lean_st_ref_set(v___x_460_, v___x_462_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_463_);
v___x_465_ = v___x_453_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v_f_448_);
v_a_468_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_450_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_450_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_registerGetEqnsFn(v_f_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_489_; lean_object* v_env_490_; uint8_t v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_st_ref_get(v_a_483_);
v_env_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_ref(v_env_490_);
lean_dec(v___x_489_);
v___x_491_ = 0;
lean_inc(v_declName_479_);
v___x_492_ = l_Lean_Environment_findAsync_x3f(v_env_490_, v_declName_479_, v___x_491_);
if (lean_obj_tag(v___x_492_) == 1)
{
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_520_; 
v_val_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_520_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_520_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_520_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
uint8_t v_kind_497_; 
v_kind_497_ = lean_ctor_get_uint8(v_val_493_, sizeof(void*)*3);
if (v_kind_497_ == 0)
{
lean_object* v_sig_498_; lean_object* v___x_499_; lean_object* v_env_500_; uint8_t v___x_501_; 
v_sig_498_ = lean_ctor_get(v_val_493_, 1);
lean_inc_ref(v_sig_498_);
lean_dec(v_val_493_);
v___x_499_ = lean_st_ref_get(v_a_483_);
v_env_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc_ref(v_env_500_);
lean_dec(v___x_499_);
v___x_501_ = l_Lean_Meta_isMatcherCore(v_env_500_, v_declName_479_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v_type_503_; lean_object* v___x_504_; 
lean_del_object(v___x_495_);
v___x_502_ = lean_task_get_own(v_sig_498_);
v_type_503_ = lean_ctor_get(v___x_502_, 2);
lean_inc_ref(v_type_503_);
lean_dec(v___x_502_);
v___x_504_ = l_Lean_Meta_isProp(v_type_503_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_515_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_509_ = lean_unbox(v_a_505_);
lean_dec(v_a_505_);
v___x_510_ = lean_bool_not(v___x_509_);
v___x_511_ = lean_box(v___x_510_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
return v___x_504_;
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec_ref(v_sig_498_);
v___x_516_ = lean_box(v___x_491_);
if (v_isShared_496_ == 0)
{
lean_ctor_set_tag(v___x_495_, 0);
lean_ctor_set(v___x_495_, 0, v___x_516_);
v___x_518_ = v___x_495_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_del_object(v___x_495_);
lean_dec(v_val_493_);
lean_dec(v_declName_479_);
goto v___jp_485_;
}
}
}
else
{
lean_dec(v___x_492_);
lean_dec(v_declName_479_);
goto v___jp_485_;
}
v___jp_485_:
{
uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = 0;
v___x_487_ = lean_box(v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_536_);
return v_res_538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_539_; lean_object* v___f_540_; 
v___x_539_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_540_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_540_, 0, v___x_539_);
return v___f_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___f_542_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_box(1);
v___x_545_ = l_Lean_registerEnvExtension___redArg(v___f_542_, v___x_543_, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_547_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_548_, lean_object* v_opt_549_){
_start:
{
lean_object* v_name_550_; lean_object* v_defValue_551_; lean_object* v_map_552_; lean_object* v___x_553_; 
v_name_550_ = lean_ctor_get(v_opt_549_, 0);
v_defValue_551_ = lean_ctor_get(v_opt_549_, 1);
v_map_552_ = lean_ctor_get(v_opts_548_, 0);
v___x_553_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_552_, v_name_550_);
if (lean_obj_tag(v___x_553_) == 0)
{
uint8_t v___x_554_; 
v___x_554_ = lean_unbox(v_defValue_551_);
return v___x_554_;
}
else
{
lean_object* v_val_555_; 
v_val_555_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v___x_553_, 1);
if (lean_obj_tag(v_val_555_) == 1)
{
uint8_t v_v_556_; 
v_v_556_ = lean_ctor_get_uint8(v_val_555_, 0);
lean_dec_ref_known(v_val_555_, 0);
return v_v_556_;
}
else
{
uint8_t v___x_557_; 
lean_dec(v_val_555_);
v___x_557_ = lean_unbox(v_defValue_551_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_558_, lean_object* v_opt_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_558_, v_opt_559_);
lean_dec_ref(v_opt_559_);
lean_dec_ref(v_opts_558_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_opts_562_, lean_object* v_opt_563_){
_start:
{
lean_object* v_name_564_; lean_object* v_defValue_565_; lean_object* v_map_566_; lean_object* v___x_567_; 
v_name_564_ = lean_ctor_get(v_opt_563_, 0);
v_defValue_565_ = lean_ctor_get(v_opt_563_, 1);
v_map_566_ = lean_ctor_get(v_opts_562_, 0);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_566_, v_name_564_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_inc(v_defValue_565_);
return v_defValue_565_;
}
else
{
lean_object* v_val_568_; 
v_val_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v___x_567_, 1);
if (lean_obj_tag(v_val_568_) == 3)
{
lean_object* v_v_569_; 
v_v_569_ = lean_ctor_get(v_val_568_, 0);
lean_inc(v_v_569_);
lean_dec_ref_known(v_val_568_, 1);
return v_v_569_;
}
else
{
lean_dec(v_val_568_);
lean_inc(v_defValue_565_);
return v_defValue_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_opts_570_, lean_object* v_opt_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_570_, v_opt_571_);
lean_dec_ref(v_opt_571_);
lean_dec_ref(v_opts_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_576_, size_t v_sz_577_, size_t v_i_578_, lean_object* v_b_579_){
_start:
{
lean_object* v_a_581_; uint8_t v___x_585_; 
v___x_585_ = lean_usize_dec_lt(v_i_578_, v_sz_577_);
if (v___x_585_ == 0)
{
return v_b_579_;
}
else
{
lean_object* v_a_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v_map_589_; uint8_t v_hasTrace_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_603_; 
v_a_586_ = lean_array_uget_borrowed(v_as_576_, v_i_578_);
v_fst_587_ = lean_ctor_get(v_a_586_, 0);
v_snd_588_ = lean_ctor_get(v_a_586_, 1);
v_map_589_ = lean_ctor_get(v_b_579_, 0);
v_hasTrace_590_ = lean_ctor_get_uint8(v_b_579_, sizeof(void*)*1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_b_579_);
if (v_isSharedCheck_603_ == 0)
{
v___x_592_ = v_b_579_;
v_isShared_593_ = v_isSharedCheck_603_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_map_589_);
lean_dec(v_b_579_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_603_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; 
lean_inc(v_snd_588_);
lean_inc(v_fst_587_);
v___x_594_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_587_, v_snd_588_, v_map_589_);
if (v_hasTrace_590_ == 0)
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_598_; 
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_596_ = l_Lean_Name_isPrefixOf(v___x_595_, v_fst_587_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_594_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*1, v___x_596_);
v_a_581_ = v___x_598_;
goto v___jp_580_;
}
}
else
{
lean_object* v___x_601_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_601_ = v___x_592_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_594_);
lean_ctor_set_uint8(v_reuseFailAlloc_602_, sizeof(void*)*1, v_hasTrace_590_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
v_a_581_ = v___x_601_;
goto v___jp_580_;
}
}
}
}
v___jp_580_:
{
size_t v___x_582_; size_t v___x_583_; 
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_578_, v___x_582_);
v_i_578_ = v___x_583_;
v_b_579_ = v_a_581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_604_, lean_object* v_sz_605_, lean_object* v_i_606_, lean_object* v_b_607_){
_start:
{
size_t v_sz_boxed_608_; size_t v_i_boxed_609_; lean_object* v_res_610_; 
v_sz_boxed_608_ = lean_unbox_usize(v_sz_605_);
lean_dec(v_sz_605_);
v_i_boxed_609_ = lean_unbox_usize(v_i_606_);
lean_dec(v_i_606_);
v_res_610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_as_604_, v_sz_boxed_608_, v_i_boxed_609_, v_b_607_);
lean_dec_ref(v_as_604_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_611_, lean_object* v_k_612_, uint8_t v_v_613_){
_start:
{
lean_object* v_map_614_; uint8_t v_hasTrace_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_629_; 
v_map_614_ = lean_ctor_get(v_o_611_, 0);
v_hasTrace_615_ = lean_ctor_get_uint8(v_o_611_, sizeof(void*)*1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_o_611_);
if (v_isSharedCheck_629_ == 0)
{
v___x_617_ = v_o_611_;
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_map_614_);
lean_dec(v_o_611_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_619_, 0, v_v_613_);
lean_inc(v_k_612_);
v___x_620_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_612_, v___x_619_, v_map_614_);
if (v_hasTrace_615_ == 0)
{
lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_624_; 
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_622_ = l_Lean_Name_isPrefixOf(v___x_621_, v_k_612_);
lean_dec(v_k_612_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_620_);
v___x_624_ = v___x_617_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_620_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v___x_622_);
return v___x_624_;
}
}
else
{
lean_object* v___x_627_; 
lean_dec(v_k_612_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_620_);
v___x_627_ = v___x_617_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_628_, sizeof(void*)*1, v_hasTrace_615_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_630_, lean_object* v_k_631_, lean_object* v_v_632_){
_start:
{
uint8_t v_v_boxed_633_; lean_object* v_res_634_; 
v_v_boxed_633_ = lean_unbox(v_v_632_);
v_res_634_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_630_, v_k_631_, v_v_boxed_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_635_, lean_object* v_opt_636_, uint8_t v_val_637_){
_start:
{
lean_object* v_name_638_; lean_object* v___x_639_; 
v_name_638_ = lean_ctor_get(v_opt_636_, 0);
lean_inc(v_name_638_);
lean_dec_ref(v_opt_636_);
v___x_639_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_635_, v_name_638_, v_val_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_640_, lean_object* v_opt_641_, lean_object* v_val_642_){
_start:
{
uint8_t v_val_boxed_643_; lean_object* v_res_644_; 
v_val_boxed_643_ = lean_unbox(v_val_642_);
v_res_644_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_640_, v_opt_641_, v_val_boxed_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(lean_object* v_as_645_, size_t v_i_646_, size_t v_stop_647_, lean_object* v_b_648_){
_start:
{
uint8_t v___x_649_; 
v___x_649_ = lean_usize_dec_eq(v_i_646_, v_stop_647_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v_defValue_651_; uint8_t v___x_652_; lean_object* v___x_653_; size_t v___x_654_; size_t v___x_655_; 
v___x_650_ = lean_array_uget_borrowed(v_as_645_, v_i_646_);
v_defValue_651_ = lean_ctor_get(v___x_650_, 1);
v___x_652_ = lean_unbox(v_defValue_651_);
lean_inc(v___x_650_);
v___x_653_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_648_, v___x_650_, v___x_652_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_646_, v___x_654_);
v_i_646_ = v___x_655_;
v_b_648_ = v___x_653_;
goto _start;
}
else
{
return v_b_648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(lean_object* v_as_657_, lean_object* v_i_658_, lean_object* v_stop_659_, lean_object* v_b_660_){
_start:
{
size_t v_i_boxed_661_; size_t v_stop_boxed_662_; lean_object* v_res_663_; 
v_i_boxed_661_ = lean_unbox_usize(v_i_658_);
lean_dec(v_i_658_);
v_stop_boxed_662_ = lean_unbox_usize(v_stop_659_);
lean_dec(v_stop_659_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v_as_657_, v_i_boxed_661_, v_stop_boxed_662_, v_b_660_);
lean_dec_ref(v_as_657_);
return v_res_663_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Array_instInhabited(lean_box(0));
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = l_Lean_Meta_eqnAffectingOptions;
v___x_671_ = lean_array_get_size(v___x_670_);
return v___x_671_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_nat_dec_lt(v___x_673_, v___x_672_);
return v___x_674_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_676_ = lean_nat_dec_le(v___x_675_, v___x_675_);
return v___x_676_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__7(void){
_start:
{
lean_object* v___x_677_; size_t v___x_678_; 
v___x_677_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_678_ = lean_usize_of_nat(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_679_, lean_object* v_act_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v_fileName_689_; lean_object* v_fileMap_690_; lean_object* v_currRecDepth_691_; lean_object* v_ref_692_; lean_object* v_currNamespace_693_; lean_object* v_openDecls_694_; lean_object* v_initHeartbeats_695_; lean_object* v_maxHeartbeats_696_; lean_object* v_quotContext_697_; lean_object* v_currMacroScope_698_; lean_object* v_cancelTk_x3f_699_; uint8_t v_suppressElabErrors_700_; lean_object* v_inheritedTraceOptions_701_; lean_object* v___y_702_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_env_709_; lean_object* v___x_710_; lean_object* v_toEnvExtension_711_; lean_object* v_asyncMode_712_; lean_object* v_fileName_713_; lean_object* v_fileMap_714_; lean_object* v_options_715_; lean_object* v_currRecDepth_716_; lean_object* v_ref_717_; lean_object* v_currNamespace_718_; lean_object* v_openDecls_719_; lean_object* v_initHeartbeats_720_; lean_object* v_maxHeartbeats_721_; lean_object* v_quotContext_722_; lean_object* v_currMacroScope_723_; lean_object* v_cancelTk_x3f_724_; uint8_t v_suppressElabErrors_725_; lean_object* v_inheritedTraceOptions_726_; lean_object* v___y_728_; uint8_t v___y_729_; uint8_t v___y_730_; lean_object* v___y_753_; lean_object* v___x_759_; uint8_t v___x_760_; lean_object* v___x_761_; 
v___x_707_ = lean_st_ref_get(v_a_684_);
v___x_708_ = lean_st_ref_get(v_a_684_);
v_env_709_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_env_709_);
lean_dec(v___x_707_);
v___x_710_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_711_ = lean_ctor_get(v___x_710_, 0);
v_asyncMode_712_ = lean_ctor_get(v_toEnvExtension_711_, 2);
v_fileName_713_ = lean_ctor_get(v_a_683_, 0);
v_fileMap_714_ = lean_ctor_get(v_a_683_, 1);
v_options_715_ = lean_ctor_get(v_a_683_, 2);
v_currRecDepth_716_ = lean_ctor_get(v_a_683_, 3);
v_ref_717_ = lean_ctor_get(v_a_683_, 5);
v_currNamespace_718_ = lean_ctor_get(v_a_683_, 6);
v_openDecls_719_ = lean_ctor_get(v_a_683_, 7);
v_initHeartbeats_720_ = lean_ctor_get(v_a_683_, 8);
v_maxHeartbeats_721_ = lean_ctor_get(v_a_683_, 9);
v_quotContext_722_ = lean_ctor_get(v_a_683_, 10);
v_currMacroScope_723_ = lean_ctor_get(v_a_683_, 11);
v_cancelTk_x3f_724_ = lean_ctor_get(v_a_683_, 12);
v_suppressElabErrors_725_ = lean_ctor_get_uint8(v_a_683_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_726_ = lean_ctor_get(v_a_683_, 13);
v___x_759_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_760_ = 0;
v___x_761_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_759_, v___x_710_, v_env_709_, v_declName_679_, v_asyncMode_712_, v___x_760_);
if (lean_obj_tag(v___x_761_) == 1)
{
lean_object* v_val_762_; lean_object* v___y_764_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_val_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_768_ = l_Lean_Meta_eqnAffectingOptions;
v___x_769_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_769_ == 0)
{
lean_inc_ref(v_options_715_);
v___y_764_ = v_options_715_;
goto v___jp_763_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_770_ == 0)
{
if (v___x_769_ == 0)
{
lean_inc_ref(v_options_715_);
v___y_764_ = v_options_715_;
goto v___jp_763_;
}
else
{
size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_771_ = ((size_t)0ULL);
v___x_772_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_715_);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_768_, v___x_771_, v___x_772_, v_options_715_);
v___y_764_ = v___x_773_;
goto v___jp_763_;
}
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)0ULL);
v___x_775_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_715_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_768_, v___x_774_, v___x_775_, v_options_715_);
v___y_764_ = v___x_776_;
goto v___jp_763_;
}
}
v___jp_763_:
{
size_t v_sz_765_; size_t v___x_766_; lean_object* v___x_767_; 
v_sz_765_ = lean_array_size(v_val_762_);
v___x_766_ = ((size_t)0ULL);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_762_, v_sz_765_, v___x_766_, v___y_764_);
lean_dec(v_val_762_);
v___y_753_ = v___x_767_;
goto v___jp_752_;
}
}
else
{
lean_object* v___x_777_; uint8_t v___x_778_; 
lean_dec(v___x_761_);
v___x_777_ = l_Lean_Meta_eqnAffectingOptions;
v___x_778_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_778_ == 0)
{
lean_inc_ref(v_options_715_);
v___y_753_ = v_options_715_;
goto v___jp_752_;
}
else
{
uint8_t v___x_779_; 
v___x_779_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_779_ == 0)
{
if (v___x_778_ == 0)
{
lean_inc_ref(v_options_715_);
v___y_753_ = v_options_715_;
goto v___jp_752_;
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_715_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_777_, v___x_780_, v___x_781_, v_options_715_);
v___y_753_ = v___x_782_;
goto v___jp_752_;
}
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_715_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_777_, v___x_783_, v___x_784_, v_options_715_);
v___y_753_ = v___x_785_;
goto v___jp_752_;
}
}
}
v___jp_686_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = l_Lean_maxRecDepth;
v___x_704_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_687_, v___x_703_);
lean_inc_ref(v_inheritedTraceOptions_701_);
lean_inc(v_cancelTk_x3f_699_);
lean_inc(v_currMacroScope_698_);
lean_inc(v_quotContext_697_);
lean_inc(v_maxHeartbeats_696_);
lean_inc(v_initHeartbeats_695_);
lean_inc(v_openDecls_694_);
lean_inc(v_currNamespace_693_);
lean_inc(v_ref_692_);
lean_inc(v_currRecDepth_691_);
lean_inc_ref(v_fileMap_690_);
lean_inc_ref(v_fileName_689_);
v___x_705_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_705_, 0, v_fileName_689_);
lean_ctor_set(v___x_705_, 1, v_fileMap_690_);
lean_ctor_set(v___x_705_, 2, v___y_687_);
lean_ctor_set(v___x_705_, 3, v_currRecDepth_691_);
lean_ctor_set(v___x_705_, 4, v___x_704_);
lean_ctor_set(v___x_705_, 5, v_ref_692_);
lean_ctor_set(v___x_705_, 6, v_currNamespace_693_);
lean_ctor_set(v___x_705_, 7, v_openDecls_694_);
lean_ctor_set(v___x_705_, 8, v_initHeartbeats_695_);
lean_ctor_set(v___x_705_, 9, v_maxHeartbeats_696_);
lean_ctor_set(v___x_705_, 10, v_quotContext_697_);
lean_ctor_set(v___x_705_, 11, v_currMacroScope_698_);
lean_ctor_set(v___x_705_, 12, v_cancelTk_x3f_699_);
lean_ctor_set(v___x_705_, 13, v_inheritedTraceOptions_701_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*14, v___y_688_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*14 + 1, v_suppressElabErrors_700_);
lean_inc(v___y_702_);
lean_inc(v_a_682_);
lean_inc_ref(v_a_681_);
v___x_706_ = lean_apply_5(v_act_680_, v_a_681_, v_a_682_, v___x_705_, v___y_702_, lean_box(0));
return v___x_706_;
}
v___jp_727_:
{
uint8_t v___x_731_; 
v___x_731_ = lean_bool_not(v___y_730_);
if (v___x_731_ == 0)
{
v___y_687_ = v___y_728_;
v___y_688_ = v___y_729_;
v_fileName_689_ = v_fileName_713_;
v_fileMap_690_ = v_fileMap_714_;
v_currRecDepth_691_ = v_currRecDepth_716_;
v_ref_692_ = v_ref_717_;
v_currNamespace_693_ = v_currNamespace_718_;
v_openDecls_694_ = v_openDecls_719_;
v_initHeartbeats_695_ = v_initHeartbeats_720_;
v_maxHeartbeats_696_ = v_maxHeartbeats_721_;
v_quotContext_697_ = v_quotContext_722_;
v_currMacroScope_698_ = v_currMacroScope_723_;
v_cancelTk_x3f_699_ = v_cancelTk_x3f_724_;
v_suppressElabErrors_700_ = v_suppressElabErrors_725_;
v_inheritedTraceOptions_701_ = v_inheritedTraceOptions_726_;
v___y_702_ = v_a_684_;
goto v___jp_686_;
}
else
{
lean_object* v___x_732_; lean_object* v_env_733_; lean_object* v_nextMacroScope_734_; lean_object* v_ngen_735_; lean_object* v_auxDeclNGen_736_; lean_object* v_traceState_737_; lean_object* v_messages_738_; lean_object* v_infoState_739_; lean_object* v_snapshotTasks_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_750_; 
v___x_732_ = lean_st_ref_take(v_a_684_);
v_env_733_ = lean_ctor_get(v___x_732_, 0);
v_nextMacroScope_734_ = lean_ctor_get(v___x_732_, 1);
v_ngen_735_ = lean_ctor_get(v___x_732_, 2);
v_auxDeclNGen_736_ = lean_ctor_get(v___x_732_, 3);
v_traceState_737_ = lean_ctor_get(v___x_732_, 4);
v_messages_738_ = lean_ctor_get(v___x_732_, 6);
v_infoState_739_ = lean_ctor_get(v___x_732_, 7);
v_snapshotTasks_740_ = lean_ctor_get(v___x_732_, 8);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_732_, 5);
lean_dec(v_unused_751_);
v___x_742_ = v___x_732_;
v_isShared_743_ = v_isSharedCheck_750_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_snapshotTasks_740_);
lean_inc(v_infoState_739_);
lean_inc(v_messages_738_);
lean_inc(v_traceState_737_);
lean_inc(v_auxDeclNGen_736_);
lean_inc(v_ngen_735_);
lean_inc(v_nextMacroScope_734_);
lean_inc(v_env_733_);
lean_dec(v___x_732_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_750_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_744_ = l_Lean_Kernel_enableDiag(v_env_733_, v___y_729_);
v___x_745_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 5, v___x_745_);
lean_ctor_set(v___x_742_, 0, v___x_744_);
v___x_747_ = v___x_742_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_nextMacroScope_734_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_ngen_735_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_auxDeclNGen_736_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_traceState_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 5, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_749_, 6, v_messages_738_);
lean_ctor_set(v_reuseFailAlloc_749_, 7, v_infoState_739_);
lean_ctor_set(v_reuseFailAlloc_749_, 8, v_snapshotTasks_740_);
v___x_747_ = v_reuseFailAlloc_749_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; 
v___x_748_ = lean_st_ref_set(v_a_684_, v___x_747_);
v___y_687_ = v___y_728_;
v___y_688_ = v___y_729_;
v_fileName_689_ = v_fileName_713_;
v_fileMap_690_ = v_fileMap_714_;
v_currRecDepth_691_ = v_currRecDepth_716_;
v_ref_692_ = v_ref_717_;
v_currNamespace_693_ = v_currNamespace_718_;
v_openDecls_694_ = v_openDecls_719_;
v_initHeartbeats_695_ = v_initHeartbeats_720_;
v_maxHeartbeats_696_ = v_maxHeartbeats_721_;
v_quotContext_697_ = v_quotContext_722_;
v_currMacroScope_698_ = v_currMacroScope_723_;
v_cancelTk_x3f_699_ = v_cancelTk_x3f_724_;
v_suppressElabErrors_700_ = v_suppressElabErrors_725_;
v_inheritedTraceOptions_701_ = v_inheritedTraceOptions_726_;
v___y_702_ = v_a_684_;
goto v___jp_686_;
}
}
}
}
v___jp_752_:
{
lean_object* v_env_754_; lean_object* v___x_755_; uint8_t v___x_756_; uint8_t v___x_757_; 
v_env_754_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_env_754_);
lean_dec(v___x_708_);
v___x_755_ = l_Lean_diagnostics;
v___x_756_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_753_, v___x_755_);
v___x_757_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_754_);
lean_dec_ref(v_env_754_);
if (v___x_757_ == 0)
{
if (v___x_756_ == 0)
{
uint8_t v___x_758_; 
v___x_758_ = 1;
v___y_728_ = v___y_753_;
v___y_729_ = v___x_756_;
v___y_730_ = v___x_758_;
goto v___jp_727_;
}
else
{
v___y_728_ = v___y_753_;
v___y_729_ = v___x_756_;
v___y_730_ = v___x_757_;
goto v___jp_727_;
}
}
else
{
v___y_728_ = v___y_753_;
v___y_729_ = v___x_756_;
v___y_730_ = v___x_756_;
goto v___jp_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_786_, lean_object* v_act_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_786_, v_act_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_794_, lean_object* v_declName_795_, lean_object* v_act_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_795_, v_act_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_803_, lean_object* v_declName_804_, lean_object* v_act_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_803_, v_declName_804_, v_act_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_env_816_; lean_object* v_toConstantVal_817_; lean_object* v_value_818_; lean_object* v_all_819_; uint8_t v___y_821_; lean_object* v_type_829_; uint8_t v___x_830_; 
v___x_815_ = lean_st_ref_get(v___y_813_);
v_env_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc_ref_n(v_env_816_, 2);
lean_dec(v___x_815_);
v_toConstantVal_817_ = lean_ctor_get(v_thm_812_, 0);
v_value_818_ = lean_ctor_get(v_thm_812_, 1);
v_all_819_ = lean_ctor_get(v_thm_812_, 2);
v_type_829_ = lean_ctor_get(v_toConstantVal_817_, 2);
v___x_830_ = l_Lean_Environment_hasUnsafe(v_env_816_, v_type_829_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_Environment_hasUnsafe(v_env_816_, v_value_818_);
v___y_821_ = v___x_831_;
goto v___jp_820_;
}
else
{
lean_dec_ref(v_env_816_);
v___y_821_ = v___x_830_;
goto v___jp_820_;
}
v___jp_820_:
{
if (v___y_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_822_, 0, v_thm_812_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_inc(v_all_819_);
lean_inc_ref(v_value_818_);
lean_inc_ref(v_toConstantVal_817_);
lean_dec_ref(v_thm_812_);
v___x_824_ = lean_box(0);
v___x_825_ = 0;
v___x_826_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_826_, 0, v_toConstantVal_817_);
lean_ctor_set(v___x_826_, 1, v_value_818_);
lean_ctor_set(v___x_826_, 2, v___x_824_);
lean_ctor_set(v___x_826_, 3, v_all_819_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*4, v___x_825_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_832_, v___y_833_);
lean_dec(v___y_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_836_, v___y_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_850_, lean_object* v_b_851_, lean_object* v_c_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
v___x_858_ = lean_apply_7(v_k_850_, v_b_851_, v_c_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, lean_box(0));
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_859_, lean_object* v_b_860_, lean_object* v_c_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_859_, v_b_860_, v_c_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_868_, lean_object* v_k_869_, uint8_t v_cleanupAnnotations_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___f_876_; uint8_t v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___f_876_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_876_, 0, v_k_869_);
v___x_877_ = 1;
v___x_878_ = 0;
v___x_879_ = lean_box(0);
v___x_880_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_868_, v___x_877_, v___x_878_, v___x_877_, v___x_878_, v___x_879_, v___f_876_, v_cleanupAnnotations_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_880_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_880_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_897_, lean_object* v_k_898_, lean_object* v_cleanupAnnotations_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_905_; lean_object* v_res_906_; 
v_cleanupAnnotations_boxed_905_ = lean_unbox(v_cleanupAnnotations_899_);
v_res_906_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_897_, v_k_898_, v_cleanupAnnotations_boxed_905_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_907_, lean_object* v_e_908_, lean_object* v_k_909_, uint8_t v_cleanupAnnotations_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_908_, v_k_909_, v_cleanupAnnotations_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_917_, lean_object* v_e_918_, lean_object* v_k_919_, lean_object* v_cleanupAnnotations_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_926_; lean_object* v_res_927_; 
v_cleanupAnnotations_boxed_926_ = lean_unbox(v_cleanupAnnotations_920_);
v_res_927_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_917_, v_e_918_, v_k_919_, v_cleanupAnnotations_boxed_926_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
if (lean_obj_tag(v_a_928_) == 0)
{
lean_object* v___x_930_; 
v___x_930_ = l_List_reverse___redArg(v_a_929_);
return v___x_930_;
}
else
{
lean_object* v_head_931_; lean_object* v_tail_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_941_; 
v_head_931_ = lean_ctor_get(v_a_928_, 0);
v_tail_932_ = lean_ctor_get(v_a_928_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_941_ == 0)
{
v___x_934_ = v_a_928_;
v_isShared_935_ = v_isSharedCheck_941_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_tail_932_);
lean_inc(v_head_931_);
lean_dec(v_a_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_941_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_mkLevelParam(v_head_931_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_a_929_);
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_a_929_);
v___x_938_ = v_reuseFailAlloc_940_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
v_a_928_ = v_tail_932_;
v_a_929_ = v___x_938_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_942_, lean_object* v_name_943_, lean_object* v_xs_944_, lean_object* v_body_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_name_951_; lean_object* v_levelParams_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_1022_; 
v_name_951_ = lean_ctor_get(v_toConstantVal_942_, 0);
v_levelParams_952_ = lean_ctor_get(v_toConstantVal_942_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_toConstantVal_942_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_toConstantVal_942_, 2);
lean_dec(v_unused_1023_);
v___x_954_ = v_toConstantVal_942_;
v_isShared_955_ = v_isSharedCheck_1022_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_levelParams_952_);
lean_inc(v_name_951_);
lean_dec(v_toConstantVal_942_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_1022_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_lhs_959_; lean_object* v___x_960_; 
v___x_956_ = lean_box(0);
lean_inc(v_levelParams_952_);
v___x_957_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_952_, v___x_956_);
v___x_958_ = l_Lean_mkConst(v_name_951_, v___x_957_);
v_lhs_959_ = l_Lean_mkAppN(v___x_958_, v_xs_944_);
lean_inc_ref(v_lhs_959_);
v___x_960_ = l_Lean_Meta_mkEq(v_lhs_959_, v_body_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; uint8_t v___x_962_; uint8_t v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = 0;
v___x_963_ = 1;
v___x_964_ = 1;
v___x_965_ = l_Lean_Meta_mkForallFVars(v_xs_944_, v_a_961_, v___x_962_, v___x_963_, v___x_963_, v___x_964_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Meta_letToHave(v_a_966_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = l_Lean_Meta_mkEqRefl(v_lhs_959_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_Meta_mkLambdaFVars(v_xs_944_, v_a_970_, v___x_962_, v___x_963_, v___x_962_, v___x_963_, v___x_964_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
lean_inc(v_name_943_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 2, v_a_968_);
lean_ctor_set(v___x_954_, 0, v_name_943_);
v___x_974_ = v___x_954_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_name_943_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_levelParams_952_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_a_968_);
v___x_974_ = v_reuseFailAlloc_981_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_a_978_; lean_object* v___x_979_; 
lean_inc(v_name_943_);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v_name_943_);
lean_ctor_set(v___x_975_, 1, v___x_956_);
v___x_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v_a_972_);
lean_ctor_set(v___x_976_, 2, v___x_975_);
v___x_977_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_976_, v___y_949_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
v___x_979_ = l_Lean_addDecl(v_a_978_, v___x_962_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v___x_980_; 
lean_dec_ref_known(v___x_979_, 1);
v___x_980_ = l_Lean_inferDefEqAttr(v_name_943_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_980_;
}
else
{
lean_dec(v_name_943_);
return v___x_979_;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_a_968_);
lean_del_object(v___x_954_);
lean_dec(v_levelParams_952_);
lean_dec(v_name_943_);
v_a_982_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_971_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_971_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_968_);
lean_del_object(v___x_954_);
lean_dec(v_levelParams_952_);
lean_dec(v_name_943_);
v_a_990_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_969_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_969_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_lhs_959_);
lean_del_object(v___x_954_);
lean_dec(v_levelParams_952_);
lean_dec(v_name_943_);
v_a_998_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_967_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_967_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v_lhs_959_);
lean_del_object(v___x_954_);
lean_dec(v_levelParams_952_);
lean_dec(v_name_943_);
v_a_1006_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_965_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_965_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v_lhs_959_);
lean_del_object(v___x_954_);
lean_dec(v_levelParams_952_);
lean_dec(v_name_943_);
v_a_1014_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_960_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_960_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1024_, lean_object* v_name_1025_, lean_object* v_xs_1026_, lean_object* v_body_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1024_, v_name_1025_, v_xs_1026_, v_body_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_xs_1026_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1034_, lean_object* v_info_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_toConstantVal_1041_; lean_object* v_value_1042_; lean_object* v___f_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; 
v_toConstantVal_1041_ = lean_ctor_get(v_info_1035_, 0);
lean_inc_ref(v_toConstantVal_1041_);
v_value_1042_ = lean_ctor_get(v_info_1035_, 1);
lean_inc_ref(v_value_1042_);
lean_dec_ref(v_info_1035_);
v___f_1043_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1043_, 0, v_toConstantVal_1041_);
lean_closure_set(v___f_1043_, 1, v_name_1034_);
v___x_1044_ = 1;
v___x_1045_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1042_, v___f_1043_, v___x_1044_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1046_, lean_object* v_info_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1046_, v_info_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1054_, lean_object* v_name_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1064_; lean_object* v_env_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = lean_st_ref_get(v_a_1059_);
v_env_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_ref(v_env_1065_);
lean_dec(v___x_1064_);
v___x_1066_ = 0;
lean_inc(v_declName_1054_);
v___x_1067_ = l_Lean_Environment_find_x3f(v_env_1065_, v_declName_1054_, v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 1)
{
lean_object* v_val_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1095_; 
v_val_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1095_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_val_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1095_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
if (lean_obj_tag(v_val_1068_) == 1)
{
lean_object* v_val_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_val_1072_ = lean_ctor_get(v_val_1068_, 0);
lean_inc_ref(v_val_1072_);
lean_dec_ref_known(v_val_1068_, 1);
lean_inc_n(v_name_1055_, 2);
v___x_1073_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1073_, 0, v_name_1055_);
lean_closure_set(v___x_1073_, 1, v_val_1072_);
lean_inc(v_declName_1054_);
v___x_1074_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1074_, 0, lean_box(0));
lean_closure_set(v___x_1074_, 1, v_declName_1054_);
lean_closure_set(v___x_1074_, 2, v___x_1073_);
v___x_1075_ = l_Lean_Meta_realizeConst(v_declName_1054_, v_name_1055_, v___x_1074_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1085_; 
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v___x_1075_, 0);
lean_dec(v_unused_1086_);
v___x_1077_ = v___x_1075_;
v_isShared_1078_ = v_isSharedCheck_1085_;
goto v_resetjp_1076_;
}
else
{
lean_dec(v___x_1075_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1085_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v_name_1055_);
v___x_1080_ = v___x_1070_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_name_1055_);
v___x_1080_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1080_);
v___x_1082_ = v___x_1077_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_del_object(v___x_1070_);
lean_dec(v_name_1055_);
v_a_1087_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1075_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1075_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_del_object(v___x_1070_);
lean_dec(v_val_1068_);
lean_dec(v_name_1055_);
lean_dec(v_declName_1054_);
goto v___jp_1061_;
}
}
}
else
{
lean_dec(v___x_1067_);
lean_dec(v_name_1055_);
lean_dec(v_declName_1054_);
goto v___jp_1061_;
}
v___jp_1061_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1096_, lean_object* v_name_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1096_, v_name_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1104_, lean_object* v_vals_1105_, lean_object* v_i_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_array_get_size(v_keys_1104_);
v___x_1109_ = lean_nat_dec_lt(v_i_1106_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec(v_i_1106_);
v___x_1110_ = lean_box(0);
return v___x_1110_;
}
else
{
lean_object* v_k_x27_1111_; uint8_t v___x_1112_; 
v_k_x27_1111_ = lean_array_fget_borrowed(v_keys_1104_, v_i_1106_);
v___x_1112_ = lean_name_eq(v_k_1107_, v_k_x27_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v_i_1106_, v___x_1113_);
lean_dec(v_i_1106_);
v_i_1106_ = v___x_1114_;
goto _start;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_array_fget_borrowed(v_vals_1105_, v_i_1106_);
lean_dec(v_i_1106_);
lean_inc(v___x_1116_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1118_, lean_object* v_vals_1119_, lean_object* v_i_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1118_, v_vals_1119_, v_i_1120_, v_k_1121_);
lean_dec(v_k_1121_);
lean_dec_ref(v_vals_1119_);
lean_dec_ref(v_keys_1118_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1123_, size_t v_x_1124_, lean_object* v_x_1125_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
lean_object* v_es_1126_; lean_object* v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; lean_object* v_j_1130_; lean_object* v___x_1131_; 
v_es_1126_ = lean_ctor_get(v_x_1123_, 0);
v___x_1127_ = lean_box(2);
v___x_1128_ = ((size_t)31ULL);
v___x_1129_ = lean_usize_land(v_x_1124_, v___x_1128_);
v_j_1130_ = lean_usize_to_nat(v___x_1129_);
v___x_1131_ = lean_array_get_borrowed(v___x_1127_, v_es_1126_, v_j_1130_);
lean_dec(v_j_1130_);
switch(lean_obj_tag(v___x_1131_))
{
case 0:
{
lean_object* v_key_1132_; lean_object* v_val_1133_; uint8_t v___x_1134_; 
v_key_1132_ = lean_ctor_get(v___x_1131_, 0);
v_val_1133_ = lean_ctor_get(v___x_1131_, 1);
v___x_1134_ = lean_name_eq(v_x_1125_, v_key_1132_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_box(0);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; 
lean_inc(v_val_1133_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_val_1133_);
return v___x_1136_;
}
}
case 1:
{
lean_object* v_node_1137_; size_t v___x_1138_; size_t v___x_1139_; 
v_node_1137_ = lean_ctor_get(v___x_1131_, 0);
v___x_1138_ = ((size_t)5ULL);
v___x_1139_ = lean_usize_shift_right(v_x_1124_, v___x_1138_);
v_x_1123_ = v_node_1137_;
v_x_1124_ = v___x_1139_;
goto _start;
}
default: 
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_box(0);
return v___x_1141_;
}
}
}
else
{
lean_object* v_ks_1142_; lean_object* v_vs_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_ks_1142_ = lean_ctor_get(v_x_1123_, 0);
v_vs_1143_ = lean_ctor_get(v_x_1123_, 1);
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1142_, v_vs_1143_, v___x_1144_, v_x_1125_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
size_t v_x_339__boxed_1149_; lean_object* v_res_1150_; 
v_x_339__boxed_1149_ = lean_unbox_usize(v_x_1147_);
lean_dec(v_x_1147_);
v_res_1150_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1146_, v_x_339__boxed_1149_, v_x_1148_);
lean_dec(v_x_1148_);
lean_dec_ref(v_x_1146_);
return v_res_1150_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1151_; uint64_t v___x_1152_; 
v___x_1151_ = lean_unsigned_to_nat(1723u);
v___x_1152_ = lean_uint64_of_nat(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
uint64_t v___y_1156_; 
if (lean_obj_tag(v_x_1154_) == 0)
{
uint64_t v___x_1159_; 
v___x_1159_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1156_ = v___x_1159_;
goto v___jp_1155_;
}
else
{
uint64_t v_hash_1160_; 
v_hash_1160_ = lean_ctor_get_uint64(v_x_1154_, sizeof(void*)*2);
v___y_1156_ = v_hash_1160_;
goto v___jp_1155_;
}
v___jp_1155_:
{
size_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_uint64_to_usize(v___y_1156_);
v___x_1158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1153_, v___x_1157_, v_x_1154_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1161_, v_x_1162_);
lean_dec(v_x_1162_);
lean_dec_ref(v_x_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v_env_1168_; lean_object* v___x_1169_; lean_object* v_asyncMode_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1167_ = lean_st_ref_get(v_a_1165_);
v_env_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc_ref(v_env_1168_);
lean_dec(v___x_1167_);
v___x_1169_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1170_ = lean_ctor_get(v___x_1169_, 2);
v___x_1171_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1172_ = lean_box(0);
v___x_1173_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1171_, v___x_1169_, v_env_1168_, v_asyncMode_1170_, v___x_1172_);
v___x_1174_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1173_, v_thmName_1164_);
lean_dec(v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec(v_thmName_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1180_, v_a_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_thmName_1185_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1191_, v_x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1194_, v_x_1195_, v_x_1196_);
lean_dec(v_x_1196_);
lean_dec_ref(v_x_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1198_, lean_object* v_x_1199_, size_t v_x_1200_, lean_object* v_x_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1199_, v_x_1200_, v_x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1203_, lean_object* v_x_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
size_t v_x_438__boxed_1207_; lean_object* v_res_1208_; 
v_x_438__boxed_1207_ = lean_unbox_usize(v_x_1205_);
lean_dec(v_x_1205_);
v_res_1208_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1203_, v_x_1204_, v_x_438__boxed_1207_, v_x_1206_);
lean_dec(v_x_1206_);
lean_dec_ref(v_x_1204_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1209_, lean_object* v_keys_1210_, lean_object* v_vals_1211_, lean_object* v_heq_1212_, lean_object* v_i_1213_, lean_object* v_k_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1210_, v_vals_1211_, v_i_1213_, v_k_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1216_, lean_object* v_keys_1217_, lean_object* v_vals_1218_, lean_object* v_heq_1219_, lean_object* v_i_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1216_, v_keys_1217_, v_vals_1218_, v_heq_1219_, v_i_1220_, v_k_1221_);
lean_dec(v_k_1221_);
lean_dec_ref(v_vals_1218_);
lean_dec_ref(v_keys_1217_);
return v_res_1222_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1223_, lean_object* v_i_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_array_get_size(v_keys_1223_);
v___x_1227_ = lean_nat_dec_lt(v_i_1224_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_dec(v_i_1224_);
return v___x_1227_;
}
else
{
lean_object* v_k_x27_1228_; uint8_t v___x_1229_; 
v_k_x27_1228_ = lean_array_fget_borrowed(v_keys_1223_, v_i_1224_);
v___x_1229_ = lean_name_eq(v_k_1225_, v_k_x27_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_i_1224_, v___x_1230_);
lean_dec(v_i_1224_);
v_i_1224_ = v___x_1231_;
goto _start;
}
else
{
lean_dec(v_i_1224_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1233_, lean_object* v_i_1234_, lean_object* v_k_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1233_, v_i_1234_, v_k_1235_);
lean_dec(v_k_1235_);
lean_dec_ref(v_keys_1233_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1238_, size_t v_x_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1238_) == 0)
{
lean_object* v_es_1241_; lean_object* v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; lean_object* v_j_1245_; lean_object* v___x_1246_; 
v_es_1241_ = lean_ctor_get(v_x_1238_, 0);
v___x_1242_ = lean_box(2);
v___x_1243_ = ((size_t)31ULL);
v___x_1244_ = lean_usize_land(v_x_1239_, v___x_1243_);
v_j_1245_ = lean_usize_to_nat(v___x_1244_);
v___x_1246_ = lean_array_get_borrowed(v___x_1242_, v_es_1241_, v_j_1245_);
lean_dec(v_j_1245_);
switch(lean_obj_tag(v___x_1246_))
{
case 0:
{
lean_object* v_key_1247_; uint8_t v___x_1248_; 
v_key_1247_ = lean_ctor_get(v___x_1246_, 0);
v___x_1248_ = lean_name_eq(v_x_1240_, v_key_1247_);
return v___x_1248_;
}
case 1:
{
lean_object* v_node_1249_; size_t v___x_1250_; size_t v___x_1251_; 
v_node_1249_ = lean_ctor_get(v___x_1246_, 0);
v___x_1250_ = ((size_t)5ULL);
v___x_1251_ = lean_usize_shift_right(v_x_1239_, v___x_1250_);
v_x_1238_ = v_node_1249_;
v_x_1239_ = v___x_1251_;
goto _start;
}
default: 
{
uint8_t v___x_1253_; 
v___x_1253_ = 0;
return v___x_1253_;
}
}
}
else
{
lean_object* v_ks_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_ks_1254_ = lean_ctor_get(v_x_1238_, 0);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1254_, v___x_1255_, v_x_1240_);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
size_t v_x_325__boxed_1260_; uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_x_325__boxed_1260_ = lean_unbox_usize(v_x_1258_);
lean_dec(v_x_1258_);
v_res_1261_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1257_, v_x_325__boxed_1260_, v_x_1259_);
lean_dec(v_x_1259_);
lean_dec_ref(v_x_1257_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
uint64_t v___y_1266_; 
if (lean_obj_tag(v_x_1264_) == 0)
{
uint64_t v___x_1269_; 
v___x_1269_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1266_ = v___x_1269_;
goto v___jp_1265_;
}
else
{
uint64_t v_hash_1270_; 
v_hash_1270_ = lean_ctor_get_uint64(v_x_1264_, sizeof(void*)*2);
v___y_1266_ = v_hash_1270_;
goto v___jp_1265_;
}
v___jp_1265_:
{
size_t v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = lean_uint64_to_usize(v___y_1266_);
v___x_1268_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1263_, v___x_1267_, v_x_1264_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
uint8_t v_res_1273_; lean_object* v_r_1274_; 
v_res_1273_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1271_, v_x_1272_);
lean_dec(v_x_1272_);
lean_dec_ref(v_x_1271_);
v_r_1274_ = lean_box(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v_env_1279_; lean_object* v___x_1280_; lean_object* v_asyncMode_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1278_ = lean_st_ref_get(v_a_1276_);
v_env_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc_ref(v_env_1279_);
lean_dec(v___x_1278_);
v___x_1280_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1281_ = lean_ctor_get(v___x_1280_, 2);
v___x_1282_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1283_ = lean_box(0);
v___x_1284_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1282_, v___x_1280_, v_env_1279_, v_asyncMode_1281_, v___x_1283_);
v___x_1285_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1284_, v_thmName_1275_);
lean_dec(v___x_1284_);
v___x_1286_ = lean_box(v___x_1285_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec(v_thmName_1288_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1292_, v_a_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Meta_isEqnThm(v_thmName_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_thmName_1297_);
return v_res_1301_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1303_, v_x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
uint8_t v_res_1309_; lean_object* v_r_1310_; 
v_res_1309_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1306_, v_x_1307_, v_x_1308_);
lean_dec(v_x_1308_);
lean_dec_ref(v_x_1307_);
v_r_1310_ = lean_box(v_res_1309_);
return v_r_1310_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1311_, lean_object* v_x_1312_, size_t v_x_1313_, lean_object* v_x_1314_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1312_, v_x_1313_, v_x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
size_t v_x_417__boxed_1320_; uint8_t v_res_1321_; lean_object* v_r_1322_; 
v_x_417__boxed_1320_ = lean_unbox_usize(v_x_1318_);
lean_dec(v_x_1318_);
v_res_1321_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1316_, v_x_1317_, v_x_417__boxed_1320_, v_x_1319_);
lean_dec(v_x_1319_);
lean_dec_ref(v_x_1317_);
v_r_1322_ = lean_box(v_res_1321_);
return v_r_1322_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1323_, lean_object* v_keys_1324_, lean_object* v_vals_1325_, lean_object* v_heq_1326_, lean_object* v_i_1327_, lean_object* v_k_1328_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1324_, v_i_1327_, v_k_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1330_, lean_object* v_keys_1331_, lean_object* v_vals_1332_, lean_object* v_heq_1333_, lean_object* v_i_1334_, lean_object* v_k_1335_){
_start:
{
uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_res_1336_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1330_, v_keys_1331_, v_vals_1332_, v_heq_1333_, v_i_1334_, v_k_1335_);
lean_dec(v_k_1335_);
lean_dec_ref(v_vals_1332_);
lean_dec_ref(v_keys_1331_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v_ks_1342_; lean_object* v_vs_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1367_; 
v_ks_1342_ = lean_ctor_get(v_x_1338_, 0);
v_vs_1343_ = lean_ctor_get(v_x_1338_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1345_ = v_x_1338_;
v_isShared_1346_ = v_isSharedCheck_1367_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_vs_1343_);
lean_inc(v_ks_1342_);
lean_dec(v_x_1338_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1367_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = lean_array_get_size(v_ks_1342_);
v___x_1348_ = lean_nat_dec_lt(v_x_1339_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec(v_x_1339_);
v___x_1349_ = lean_array_push(v_ks_1342_, v_x_1340_);
v___x_1350_ = lean_array_push(v_vs_1343_, v_x_1341_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v___x_1350_);
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1352_ = v___x_1345_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
else
{
lean_object* v_k_x27_1354_; uint8_t v___x_1355_; 
v_k_x27_1354_ = lean_array_fget_borrowed(v_ks_1342_, v_x_1339_);
v___x_1355_ = lean_name_eq(v_x_1340_, v_k_x27_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1357_; 
if (v_isShared_1346_ == 0)
{
v___x_1357_ = v___x_1345_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_ks_1342_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_vs_1343_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_add(v_x_1339_, v___x_1358_);
lean_dec(v_x_1339_);
v_x_1338_ = v___x_1357_;
v_x_1339_ = v___x_1359_;
goto _start;
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = lean_array_fset(v_ks_1342_, v_x_1339_, v_x_1340_);
v___x_1363_ = lean_array_fset(v_vs_1343_, v_x_1339_, v_x_1341_);
lean_dec(v_x_1339_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v___x_1363_);
lean_ctor_set(v___x_1345_, 0, v___x_1362_);
v___x_1365_ = v___x_1345_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1368_, lean_object* v_k_1369_, lean_object* v_v_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1368_, v___x_1371_, v_k_1369_, v_v_1370_);
return v___x_1372_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1374_, size_t v_x_1375_, size_t v_x_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_){
_start:
{
if (lean_obj_tag(v_x_1374_) == 0)
{
lean_object* v_es_1379_; size_t v___x_1380_; size_t v___x_1381_; lean_object* v_j_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v_es_1379_ = lean_ctor_get(v_x_1374_, 0);
v___x_1380_ = ((size_t)31ULL);
v___x_1381_ = lean_usize_land(v_x_1375_, v___x_1380_);
v_j_1382_ = lean_usize_to_nat(v___x_1381_);
v___x_1383_ = lean_array_get_size(v_es_1379_);
v___x_1384_ = lean_nat_dec_lt(v_j_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_dec(v_j_1382_);
lean_dec(v_x_1378_);
lean_dec(v_x_1377_);
return v_x_1374_;
}
else
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1423_; 
lean_inc_ref(v_es_1379_);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_x_1374_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_x_1374_, 0);
lean_dec(v_unused_1424_);
v___x_1386_ = v_x_1374_;
v_isShared_1387_ = v_isSharedCheck_1423_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v_x_1374_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1423_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_v_1388_; lean_object* v___x_1389_; lean_object* v_xs_x27_1390_; lean_object* v___y_1392_; 
v_v_1388_ = lean_array_fget(v_es_1379_, v_j_1382_);
v___x_1389_ = lean_box(0);
v_xs_x27_1390_ = lean_array_fset(v_es_1379_, v_j_1382_, v___x_1389_);
switch(lean_obj_tag(v_v_1388_))
{
case 0:
{
lean_object* v_key_1397_; lean_object* v_val_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1408_; 
v_key_1397_ = lean_ctor_get(v_v_1388_, 0);
v_val_1398_ = lean_ctor_get(v_v_1388_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_v_1388_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1400_ = v_v_1388_;
v_isShared_1401_ = v_isSharedCheck_1408_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_val_1398_);
lean_inc(v_key_1397_);
lean_dec(v_v_1388_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1408_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_name_eq(v_x_1377_, v_key_1397_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_del_object(v___x_1400_);
v___x_1403_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1397_, v_val_1398_, v_x_1377_, v_x_1378_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
v___y_1392_ = v___x_1404_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_val_1398_);
lean_dec(v_key_1397_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v_x_1378_);
lean_ctor_set(v___x_1400_, 0, v_x_1377_);
v___x_1406_ = v___x_1400_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_x_1377_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_x_1378_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
v___y_1392_ = v___x_1406_;
goto v___jp_1391_;
}
}
}
}
case 1:
{
lean_object* v_node_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1421_; 
v_node_1409_ = lean_ctor_get(v_v_1388_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_v_1388_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1411_ = v_v_1388_;
v_isShared_1412_ = v_isSharedCheck_1421_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_node_1409_);
lean_dec(v_v_1388_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1421_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
size_t v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1413_ = ((size_t)5ULL);
v___x_1414_ = lean_usize_shift_right(v_x_1375_, v___x_1413_);
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_x_1376_, v___x_1415_);
v___x_1417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1409_, v___x_1414_, v___x_1416_, v_x_1377_, v_x_1378_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1417_);
v___x_1419_ = v___x_1411_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
v___y_1392_ = v___x_1419_;
goto v___jp_1391_;
}
}
}
default: 
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_x_1377_);
lean_ctor_set(v___x_1422_, 1, v_x_1378_);
v___y_1392_ = v___x_1422_;
goto v___jp_1391_;
}
}
v___jp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_array_fset(v_xs_x27_1390_, v_j_1382_, v___y_1392_);
lean_dec(v_j_1382_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1393_);
v___x_1395_ = v___x_1386_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
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
else
{
lean_object* v_ks_1425_; lean_object* v_vs_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1446_; 
v_ks_1425_ = lean_ctor_get(v_x_1374_, 0);
v_vs_1426_ = lean_ctor_get(v_x_1374_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1374_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1428_ = v_x_1374_;
v_isShared_1429_ = v_isSharedCheck_1446_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_vs_1426_);
lean_inc(v_ks_1425_);
lean_dec(v_x_1374_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1446_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_ks_1425_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_vs_1426_);
v___x_1431_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v_newNode_1432_; uint8_t v___y_1434_; size_t v___x_1440_; uint8_t v___x_1441_; 
v_newNode_1432_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1431_, v_x_1377_, v_x_1378_);
v___x_1440_ = ((size_t)7ULL);
v___x_1441_ = lean_usize_dec_le(v___x_1440_, v_x_1376_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1432_);
v___x_1443_ = lean_unsigned_to_nat(4u);
v___x_1444_ = lean_nat_dec_lt(v___x_1442_, v___x_1443_);
lean_dec(v___x_1442_);
v___y_1434_ = v___x_1444_;
goto v___jp_1433_;
}
else
{
v___y_1434_ = v___x_1441_;
goto v___jp_1433_;
}
v___jp_1433_:
{
if (v___y_1434_ == 0)
{
lean_object* v_ks_1435_; lean_object* v_vs_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_ks_1435_ = lean_ctor_get(v_newNode_1432_, 0);
lean_inc_ref(v_ks_1435_);
v_vs_1436_ = lean_ctor_get(v_newNode_1432_, 1);
lean_inc_ref(v_vs_1436_);
lean_dec_ref(v_newNode_1432_);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1376_, v_ks_1435_, v_vs_1436_, v___x_1437_, v___x_1438_);
lean_dec_ref(v_vs_1436_);
lean_dec_ref(v_ks_1435_);
return v___x_1439_;
}
else
{
return v_newNode_1432_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1447_, lean_object* v_keys_1448_, lean_object* v_vals_1449_, lean_object* v_i_1450_, lean_object* v_entries_1451_){
_start:
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = lean_array_get_size(v_keys_1448_);
v___x_1453_ = lean_nat_dec_lt(v_i_1450_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_dec(v_i_1450_);
return v_entries_1451_;
}
else
{
lean_object* v_k_1454_; lean_object* v_v_1455_; uint64_t v___y_1457_; 
v_k_1454_ = lean_array_fget_borrowed(v_keys_1448_, v_i_1450_);
v_v_1455_ = lean_array_fget_borrowed(v_vals_1449_, v_i_1450_);
if (lean_obj_tag(v_k_1454_) == 0)
{
uint64_t v___x_1468_; 
v___x_1468_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1457_ = v___x_1468_;
goto v___jp_1456_;
}
else
{
uint64_t v_hash_1469_; 
v_hash_1469_ = lean_ctor_get_uint64(v_k_1454_, sizeof(void*)*2);
v___y_1457_ = v_hash_1469_;
goto v___jp_1456_;
}
v___jp_1456_:
{
size_t v_h_1458_; size_t v___x_1459_; lean_object* v___x_1460_; size_t v___x_1461_; size_t v___x_1462_; size_t v___x_1463_; size_t v_h_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_h_1458_ = lean_uint64_to_usize(v___y_1457_);
v___x_1459_ = ((size_t)5ULL);
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = ((size_t)1ULL);
v___x_1462_ = lean_usize_sub(v_depth_1447_, v___x_1461_);
v___x_1463_ = lean_usize_mul(v___x_1459_, v___x_1462_);
v_h_1464_ = lean_usize_shift_right(v_h_1458_, v___x_1463_);
v___x_1465_ = lean_nat_add(v_i_1450_, v___x_1460_);
lean_dec(v_i_1450_);
lean_inc(v_v_1455_);
lean_inc(v_k_1454_);
v___x_1466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1451_, v_h_1464_, v_depth_1447_, v_k_1454_, v_v_1455_);
v_i_1450_ = v___x_1465_;
v_entries_1451_ = v___x_1466_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1470_, lean_object* v_keys_1471_, lean_object* v_vals_1472_, lean_object* v_i_1473_, lean_object* v_entries_1474_){
_start:
{
size_t v_depth_boxed_1475_; lean_object* v_res_1476_; 
v_depth_boxed_1475_ = lean_unbox_usize(v_depth_1470_);
lean_dec(v_depth_1470_);
v_res_1476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1475_, v_keys_1471_, v_vals_1472_, v_i_1473_, v_entries_1474_);
lean_dec_ref(v_vals_1472_);
lean_dec_ref(v_keys_1471_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1477_, lean_object* v_x_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
size_t v_x_626__boxed_1482_; size_t v_x_627__boxed_1483_; lean_object* v_res_1484_; 
v_x_626__boxed_1482_ = lean_unbox_usize(v_x_1478_);
lean_dec(v_x_1478_);
v_x_627__boxed_1483_ = lean_unbox_usize(v_x_1479_);
lean_dec(v_x_1479_);
v_res_1484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1477_, v_x_626__boxed_1482_, v_x_627__boxed_1483_, v_x_1480_, v_x_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_){
_start:
{
uint64_t v___y_1489_; 
if (lean_obj_tag(v_x_1486_) == 0)
{
uint64_t v___x_1493_; 
v___x_1493_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1489_ = v___x_1493_;
goto v___jp_1488_;
}
else
{
uint64_t v_hash_1494_; 
v_hash_1494_ = lean_ctor_get_uint64(v_x_1486_, sizeof(void*)*2);
v___y_1489_ = v_hash_1494_;
goto v___jp_1488_;
}
v___jp_1488_:
{
size_t v___x_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_uint64_to_usize(v___y_1489_);
v___x_1491_ = ((size_t)1ULL);
v___x_1492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1485_, v___x_1490_, v___x_1491_, v_x_1486_, v_x_1487_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1495_, lean_object* v_as_1496_, size_t v_i_1497_, size_t v_stop_1498_, lean_object* v_b_1499_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_eq(v_i_1497_, v_stop_1498_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; 
v___x_1501_ = lean_array_uget_borrowed(v_as_1496_, v_i_1497_);
lean_inc(v_declName_1495_);
lean_inc(v___x_1501_);
v___x_1502_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1499_, v___x_1501_, v_declName_1495_);
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1497_, v___x_1503_);
v_i_1497_ = v___x_1504_;
v_b_1499_ = v___x_1502_;
goto _start;
}
else
{
lean_dec(v_declName_1495_);
return v_b_1499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1506_, lean_object* v_as_1507_, lean_object* v_i_1508_, lean_object* v_stop_1509_, lean_object* v_b_1510_){
_start:
{
size_t v_i_boxed_1511_; size_t v_stop_boxed_1512_; lean_object* v_res_1513_; 
v_i_boxed_1511_ = lean_unbox_usize(v_i_1508_);
lean_dec(v_i_1508_);
v_stop_boxed_1512_ = lean_unbox_usize(v_stop_1509_);
lean_dec(v_stop_1509_);
v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1506_, v_as_1507_, v_i_boxed_1511_, v_stop_boxed_1512_, v_b_1510_);
lean_dec_ref(v_as_1507_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1514_, lean_object* v_declName_1515_, lean_object* v_s_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_array_get_size(v_eqThms_1514_);
v___x_1519_ = lean_nat_dec_lt(v___x_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_dec(v_declName_1515_);
return v_s_1516_;
}
else
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_nat_dec_le(v___x_1518_, v___x_1518_);
if (v___x_1520_ == 0)
{
if (v___x_1519_ == 0)
{
lean_dec(v_declName_1515_);
return v_s_1516_;
}
else
{
size_t v___x_1521_; size_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = lean_usize_of_nat(v___x_1518_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1515_, v_eqThms_1514_, v___x_1521_, v___x_1522_, v_s_1516_);
return v___x_1523_;
}
}
else
{
size_t v___x_1524_; size_t v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = ((size_t)0ULL);
v___x_1525_ = lean_usize_of_nat(v___x_1518_);
v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1515_, v_eqThms_1514_, v___x_1524_, v___x_1525_, v_s_1516_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1527_, lean_object* v_declName_1528_, lean_object* v_s_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1527_, v_declName_1528_, v_s_1529_);
lean_dec_ref(v_eqThms_1527_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1531_, lean_object* v_eqThms_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v_env_1536_; lean_object* v_nextMacroScope_1537_; lean_object* v_ngen_1538_; lean_object* v_auxDeclNGen_1539_; lean_object* v_traceState_1540_; lean_object* v_messages_1541_; lean_object* v_infoState_1542_; lean_object* v_snapshotTasks_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1559_; 
v___x_1535_ = lean_st_ref_take(v_a_1533_);
v_env_1536_ = lean_ctor_get(v___x_1535_, 0);
v_nextMacroScope_1537_ = lean_ctor_get(v___x_1535_, 1);
v_ngen_1538_ = lean_ctor_get(v___x_1535_, 2);
v_auxDeclNGen_1539_ = lean_ctor_get(v___x_1535_, 3);
v_traceState_1540_ = lean_ctor_get(v___x_1535_, 4);
v_messages_1541_ = lean_ctor_get(v___x_1535_, 6);
v_infoState_1542_ = lean_ctor_get(v___x_1535_, 7);
v_snapshotTasks_1543_ = lean_ctor_get(v___x_1535_, 8);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v___x_1535_, 5);
lean_dec(v_unused_1560_);
v___x_1545_ = v___x_1535_;
v_isShared_1546_ = v_isSharedCheck_1559_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_snapshotTasks_1543_);
lean_inc(v_infoState_1542_);
lean_inc(v_messages_1541_);
lean_inc(v_traceState_1540_);
lean_inc(v_auxDeclNGen_1539_);
lean_inc(v_ngen_1538_);
lean_inc(v_nextMacroScope_1537_);
lean_inc(v_env_1536_);
lean_dec(v___x_1535_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1559_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v_asyncMode_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1547_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1548_ = lean_ctor_get(v___x_1547_, 2);
v___f_1549_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1549_, 0, v_eqThms_1532_);
lean_closure_set(v___f_1549_, 1, v_declName_1531_);
v___x_1550_ = lean_box(0);
v___x_1551_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1547_, v_env_1536_, v___f_1549_, v_asyncMode_1548_, v___x_1550_);
v___x_1552_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 5, v___x_1552_);
lean_ctor_set(v___x_1545_, 0, v___x_1551_);
v___x_1554_ = v___x_1545_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_nextMacroScope_1537_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_ngen_1538_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_auxDeclNGen_1539_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_traceState_1540_);
lean_ctor_set(v_reuseFailAlloc_1558_, 5, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 6, v_messages_1541_);
lean_ctor_set(v_reuseFailAlloc_1558_, 7, v_infoState_1542_);
lean_ctor_set(v_reuseFailAlloc_1558_, 8, v_snapshotTasks_1543_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_st_ref_set(v_a_1533_, v___x_1554_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1561_, lean_object* v_eqThms_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1561_, v_eqThms_1562_, v_a_1563_);
lean_dec(v_a_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1566_, lean_object* v_eqThms_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1566_, v_eqThms_1567_, v_a_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1572_, lean_object* v_eqThms_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1572_, v_eqThms_1573_, v_a_1574_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_x_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1579_, v_x_1580_, v_x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1583_, lean_object* v_x_1584_, size_t v_x_1585_, size_t v_x_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1584_, v_x_1585_, v_x_1586_, v_x_1587_, v_x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_, lean_object* v_x_1595_){
_start:
{
size_t v_x_895__boxed_1596_; size_t v_x_896__boxed_1597_; lean_object* v_res_1598_; 
v_x_895__boxed_1596_ = lean_unbox_usize(v_x_1592_);
lean_dec(v_x_1592_);
v_x_896__boxed_1597_ = lean_unbox_usize(v_x_1593_);
lean_dec(v_x_1593_);
v_res_1598_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1590_, v_x_1591_, v_x_895__boxed_1596_, v_x_896__boxed_1597_, v_x_1594_, v_x_1595_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1599_, lean_object* v_n_1600_, lean_object* v_k_1601_, lean_object* v_v_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1600_, v_k_1601_, v_v_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1604_, size_t v_depth_1605_, lean_object* v_keys_1606_, lean_object* v_vals_1607_, lean_object* v_heq_1608_, lean_object* v_i_1609_, lean_object* v_entries_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1605_, v_keys_1606_, v_vals_1607_, v_i_1609_, v_entries_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1612_, lean_object* v_depth_1613_, lean_object* v_keys_1614_, lean_object* v_vals_1615_, lean_object* v_heq_1616_, lean_object* v_i_1617_, lean_object* v_entries_1618_){
_start:
{
size_t v_depth_boxed_1619_; lean_object* v_res_1620_; 
v_depth_boxed_1619_ = lean_unbox_usize(v_depth_1613_);
lean_dec(v_depth_1613_);
v_res_1620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1612_, v_depth_boxed_1619_, v_keys_1614_, v_vals_1615_, v_heq_1616_, v_i_1617_, v_entries_1618_);
lean_dec_ref(v_vals_1615_);
lean_dec_ref(v_keys_1614_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1622_, v_x_1623_, v_x_1624_, v_x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1627_, lean_object* v_env_1628_, lean_object* v_idx_1629_, lean_object* v_eqs_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_nextEq_1637_; uint8_t v___x_1638_; 
v___x_1632_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_add(v_idx_1629_, v___x_1633_);
lean_dec(v_idx_1629_);
lean_inc(v___x_1634_);
v___x_1635_ = l_Nat_reprFast(v___x_1634_);
v___x_1636_ = lean_string_append(v___x_1632_, v___x_1635_);
lean_dec_ref(v___x_1635_);
lean_inc(v_declName_1627_);
lean_inc_ref(v_env_1628_);
v_nextEq_1637_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1628_, v_declName_1627_, v___x_1636_);
v___x_1638_ = l_Lean_Environment_containsOnBranch(v_env_1628_, v_nextEq_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_dec(v_nextEq_1637_);
lean_dec(v___x_1634_);
lean_dec_ref(v_env_1628_);
lean_dec(v_declName_1627_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_eqs_1630_);
return v___x_1639_;
}
else
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_array_push(v_eqs_1630_, v_nextEq_1637_);
v_idx_1629_ = v___x_1634_;
v_eqs_1630_ = v___x_1640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1642_, lean_object* v_env_1643_, lean_object* v_idx_1644_, lean_object* v_eqs_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1642_, v_env_1643_, v_idx_1644_, v_eqs_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1648_, lean_object* v_env_1649_, lean_object* v_idx_1650_, lean_object* v_eqs_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1648_, v_env_1649_, v_idx_1650_, v_eqs_1651_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1658_, lean_object* v_env_1659_, lean_object* v_idx_1660_, lean_object* v_eqs_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1658_, v_env_1659_, v_idx_1660_, v_eqs_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v_env_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; uint8_t v___x_1676_; 
v___x_1671_ = lean_st_ref_get(v_a_1669_);
v_env_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc_ref_n(v_env_1672_, 3);
lean_dec(v___x_1671_);
v___x_1673_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1668_);
v___x_1674_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1672_, v_declName_1668_, v___x_1673_);
v___x_1675_ = 1;
lean_inc(v___x_1674_);
v___x_1676_ = l_Lean_Environment_contains(v_env_1672_, v___x_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v___x_1674_);
lean_dec_ref(v_env_1672_);
lean_dec(v_declName_1668_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1679_ = lean_unsigned_to_nat(1u);
v___x_1680_ = lean_mk_empty_array_with_capacity(v___x_1679_);
v___x_1681_ = lean_array_push(v___x_1680_, v___x_1674_);
lean_inc(v_declName_1668_);
v___x_1682_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1668_, v_env_1672_, v___x_1679_, v___x_1681_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc_n(v_a_1683_, 2);
lean_dec_ref_known(v___x_1682_, 1);
v___x_1684_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1668_, v_a_1683_, v_a_1669_);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v___x_1684_, 0);
lean_dec(v_unused_1693_);
v___x_1686_ = v___x_1684_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_dec(v___x_1684_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_a_1683_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_declName_1668_);
v_a_1694_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1682_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1682_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1702_, v_a_1703_);
lean_dec(v_a_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1706_, v_a_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1720_, lean_object* v_localInsts_1721_, lean_object* v_x_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1720_, v_localInsts_1721_, v_x_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_a_1737_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1728_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1728_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1745_, lean_object* v_localInsts_1746_, lean_object* v_x_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1745_, v_localInsts_1746_, v_x_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1754_, lean_object* v_lctx_1755_, lean_object* v_localInsts_1756_, lean_object* v_x_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1755_, v_localInsts_1756_, v_x_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1764_, lean_object* v_lctx_1765_, lean_object* v_localInsts_1766_, lean_object* v_x_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1764_, v_lctx_1765_, v_localInsts_1766_, v_x_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1777_, lean_object* v_as_x27_1778_, lean_object* v_b_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
if (lean_obj_tag(v_as_x27_1778_) == 0)
{
lean_object* v___x_1785_; 
lean_dec(v_declName_1777_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_b_1779_);
return v___x_1785_;
}
else
{
lean_object* v_head_1786_; lean_object* v_tail_1787_; lean_object* v___x_1788_; 
lean_dec_ref(v_b_1779_);
v_head_1786_ = lean_ctor_get(v_as_x27_1778_, 0);
v_tail_1787_ = lean_ctor_get(v_as_x27_1778_, 1);
lean_inc(v_head_1786_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
lean_inc(v_declName_1777_);
v___x_1788_ = lean_apply_6(v_head_1786_, v_declName_1777_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, lean_box(0));
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = lean_box(0);
if (lean_obj_tag(v_a_1789_) == 1)
{
lean_object* v_val_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1801_; 
v_val_1791_ = lean_ctor_get(v_a_1789_, 0);
lean_inc(v_val_1791_);
v___x_1792_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1777_, v_val_1791_, v___y_1783_);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v___x_1792_, 0);
lean_dec(v_unused_1802_);
v___x_1794_ = v___x_1792_;
v_isShared_1795_ = v_isSharedCheck_1801_;
goto v_resetjp_1793_;
}
else
{
lean_dec(v___x_1792_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1801_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v_a_1789_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v___x_1790_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1797_);
v___x_1799_ = v___x_1794_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
else
{
lean_object* v___x_1803_; 
lean_dec(v_a_1789_);
v___x_1803_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1778_ = v_tail_1787_;
v_b_1779_ = v___x_1803_;
goto _start;
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_declName_1777_);
v_a_1805_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1788_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1788_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1813_, lean_object* v_as_x27_1814_, lean_object* v_b_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1813_, v_as_x27_1814_, v_b_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v_as_x27_1814_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
lean_inc(v_declName_1822_);
v___x_1828_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1867_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1867_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1867_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
uint8_t v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_unbox(v_a_1829_);
lean_dec(v_a_1829_);
v___x_1834_ = lean_bool_not(v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_del_object(v___x_1831_);
lean_inc(v_declName_1822_);
v___x_1835_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1822_, v___y_1826_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
if (lean_obj_tag(v_a_1836_) == 1)
{
lean_dec_ref_known(v_a_1836_, 1);
lean_dec(v_declName_1822_);
return v___x_1835_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1838_ = lean_st_ref_get(v___x_1837_);
v___x_1839_ = lean_box(0);
v___x_1840_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1841_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1822_, v___x_1838_, v___x_1840_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___x_1838_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1854_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1854_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1854_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_fst_1846_; 
v_fst_1846_ = lean_ctor_get(v_a_1842_, 0);
lean_inc(v_fst_1846_);
lean_dec(v_a_1842_);
if (lean_obj_tag(v_fst_1846_) == 0)
{
lean_object* v___x_1848_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1839_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1839_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
else
{
lean_object* v_val_1850_; lean_object* v___x_1852_; 
v_val_1850_ = lean_ctor_get(v_fst_1846_, 0);
lean_inc(v_val_1850_);
lean_dec_ref_known(v_fst_1846_, 1);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v_val_1850_);
v___x_1852_ = v___x_1844_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_val_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_a_1855_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1841_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1841_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
else
{
lean_dec(v_declName_1822_);
return v___x_1835_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_dec(v_declName_1822_);
v___x_1863_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1863_);
v___x_1865_ = v___x_1831_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v_declName_1822_);
v_a_1868_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1828_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1828_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1882_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1883_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1886_ = lean_box(1);
v___x_1887_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1888_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v___x_1887_);
lean_ctor_set(v___x_1889_, 2, v___x_1886_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___f_1898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1898_, 0, v_declName_1892_);
v___x_1899_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1900_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1901_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1899_, v___x_1900_, v___f_1898_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1909_, lean_object* v_as_1910_, lean_object* v_as_x27_1911_, lean_object* v_b_1912_, lean_object* v_a_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1909_, v_as_x27_1911_, v_b_1912_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1920_, lean_object* v_as_1921_, lean_object* v_as_x27_1922_, lean_object* v_b_1923_, lean_object* v_a_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1920_, v_as_1921_, v_as_x27_1922_, v_b_1923_, v_a_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v_as_x27_1922_);
lean_dec(v_as_1921_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1937_ = lean_unsigned_to_nat(32u);
v___x_1938_ = lean_mk_empty_array_with_capacity(v___x_1937_);
lean_dec_ref(v___x_1938_);
v___x_1939_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1940_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1931_);
v___x_1941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1941_, 0, v_declName_1931_);
v___x_1942_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1942_, 0, lean_box(0));
lean_closure_set(v___x_1942_, 1, v_declName_1931_);
lean_closure_set(v___x_1942_, 2, v___x_1941_);
v___x_1943_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1939_, v___x_1940_, v___x_1942_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v_env_1958_; lean_object* v___x_1959_; lean_object* v_mctx_1960_; lean_object* v_lctx_1961_; lean_object* v_options_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1957_ = lean_st_ref_get(v___y_1955_);
v_env_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc_ref(v_env_1958_);
lean_dec(v___x_1957_);
v___x_1959_ = lean_st_ref_get(v___y_1953_);
v_mctx_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc_ref(v_mctx_1960_);
lean_dec(v___x_1959_);
v_lctx_1961_ = lean_ctor_get(v___y_1952_, 2);
v_options_1962_ = lean_ctor_get(v___y_1954_, 2);
lean_inc_ref(v_options_1962_);
lean_inc_ref(v_lctx_1961_);
v___x_1963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1963_, 0, v_env_1958_);
lean_ctor_set(v___x_1963_, 1, v_mctx_1960_);
lean_ctor_set(v___x_1963_, 2, v_lctx_1961_);
lean_ctor_set(v___x_1963_, 3, v_options_1962_);
v___x_1964_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v_msgData_1951_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1973_; double v___x_1974_; 
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_float_of_nat(v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1978_, lean_object* v_msg_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_ref_1985_; lean_object* v___x_1986_; lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2031_; 
v_ref_1985_ = lean_ctor_get(v___y_1982_, 5);
v___x_1986_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_2031_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2031_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v_traceState_1992_; lean_object* v_env_1993_; lean_object* v_nextMacroScope_1994_; lean_object* v_ngen_1995_; lean_object* v_auxDeclNGen_1996_; lean_object* v_cache_1997_; lean_object* v_messages_1998_; lean_object* v_infoState_1999_; lean_object* v_snapshotTasks_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2030_; 
v___x_1991_ = lean_st_ref_take(v___y_1983_);
v_traceState_1992_ = lean_ctor_get(v___x_1991_, 4);
v_env_1993_ = lean_ctor_get(v___x_1991_, 0);
v_nextMacroScope_1994_ = lean_ctor_get(v___x_1991_, 1);
v_ngen_1995_ = lean_ctor_get(v___x_1991_, 2);
v_auxDeclNGen_1996_ = lean_ctor_get(v___x_1991_, 3);
v_cache_1997_ = lean_ctor_get(v___x_1991_, 5);
v_messages_1998_ = lean_ctor_get(v___x_1991_, 6);
v_infoState_1999_ = lean_ctor_get(v___x_1991_, 7);
v_snapshotTasks_2000_ = lean_ctor_get(v___x_1991_, 8);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2002_ = v___x_1991_;
v_isShared_2003_ = v_isSharedCheck_2030_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_snapshotTasks_2000_);
lean_inc(v_infoState_1999_);
lean_inc(v_messages_1998_);
lean_inc(v_cache_1997_);
lean_inc(v_traceState_1992_);
lean_inc(v_auxDeclNGen_1996_);
lean_inc(v_ngen_1995_);
lean_inc(v_nextMacroScope_1994_);
lean_inc(v_env_1993_);
lean_dec(v___x_1991_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2030_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
uint64_t v_tid_2004_; lean_object* v_traces_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2029_; 
v_tid_2004_ = lean_ctor_get_uint64(v_traceState_1992_, sizeof(void*)*1);
v_traces_2005_ = lean_ctor_get(v_traceState_1992_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_traceState_1992_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2007_ = v_traceState_1992_;
v_isShared_2008_ = v_isSharedCheck_2029_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_traces_2005_);
lean_dec(v_traceState_1992_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2029_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; double v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_2011_ = 0;
v___x_2012_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_2013_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2013_, 0, v_cls_1978_);
lean_ctor_set(v___x_2013_, 1, v___x_2009_);
lean_ctor_set(v___x_2013_, 2, v___x_2012_);
lean_ctor_set_float(v___x_2013_, sizeof(void*)*3, v___x_2010_);
lean_ctor_set_float(v___x_2013_, sizeof(void*)*3 + 8, v___x_2010_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*3 + 16, v___x_2011_);
v___x_2014_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_2015_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v_a_1987_);
lean_ctor_set(v___x_2015_, 2, v___x_2014_);
lean_inc(v_ref_1985_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_ref_1985_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_PersistentArray_push___redArg(v_traces_2005_, v___x_2016_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2017_);
v___x_2019_ = v___x_2007_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2017_);
lean_ctor_set_uint64(v_reuseFailAlloc_2028_, sizeof(void*)*1, v_tid_2004_);
v___x_2019_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 4, v___x_2019_);
v___x_2021_ = v___x_2002_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_env_1993_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_nextMacroScope_1994_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_ngen_1995_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_auxDeclNGen_1996_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2027_, 5, v_cache_1997_);
lean_ctor_set(v_reuseFailAlloc_2027_, 6, v_messages_1998_);
lean_ctor_set(v_reuseFailAlloc_2027_, 7, v_infoState_1999_);
lean_ctor_set(v_reuseFailAlloc_2027_, 8, v_snapshotTasks_2000_);
v___x_2021_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2022_ = lean_st_ref_set(v___y_1983_, v___x_2021_);
v___x_2023_ = lean_box(0);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2023_);
v___x_2025_ = v___x_1989_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2032_, lean_object* v_msg_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2032_, v_msg_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2040_, lean_object* v_as_2041_, size_t v_sz_2042_, size_t v_i_2043_, lean_object* v_b_2044_){
_start:
{
lean_object* v_a_2047_; uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2043_, v_sz_2042_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_b_2044_);
return v___x_2052_;
}
else
{
lean_object* v_a_2053_; lean_object* v_defValue_2054_; uint8_t v___x_2055_; uint8_t v___y_2057_; 
v_a_2053_ = lean_array_uget(v_as_2041_, v_i_2043_);
v_defValue_2054_ = lean_ctor_get(v_a_2053_, 1);
v___x_2055_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2040_, v_a_2053_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_unbox(v_defValue_2054_);
if (v___x_2070_ == 0)
{
v___y_2057_ = v___x_2051_;
goto v___jp_2056_;
}
else
{
v___y_2057_ = v___x_2055_;
goto v___jp_2056_;
}
}
else
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_unbox(v_defValue_2054_);
v___y_2057_ = v___x_2071_;
goto v___jp_2056_;
}
v___jp_2056_:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_bool_not(v___y_2057_);
if (v___x_2058_ == 0)
{
lean_dec(v_a_2053_);
v_a_2047_ = v_b_2044_;
goto v___jp_2046_;
}
else
{
lean_object* v_name_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2068_; 
v_name_2059_ = lean_ctor_get(v_a_2053_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_a_2053_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v_a_2053_, 1);
lean_dec(v_unused_2069_);
v___x_2061_ = v_a_2053_;
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_name_2059_);
lean_dec(v_a_2053_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2063_, 0, v___x_2055_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v___x_2063_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_name_2059_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_array_push(v_b_2044_, v___x_2065_);
v_a_2047_ = v___x_2066_;
goto v___jp_2046_;
}
}
}
}
}
v___jp_2046_:
{
size_t v___x_2048_; size_t v___x_2049_; 
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2043_, v___x_2048_);
v_i_2043_ = v___x_2049_;
v_b_2044_ = v_a_2047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2072_, lean_object* v_as_2073_, lean_object* v_sz_2074_, lean_object* v_i_2075_, lean_object* v_b_2076_, lean_object* v___y_2077_){
_start:
{
size_t v_sz_boxed_2078_; size_t v_i_boxed_2079_; lean_object* v_res_2080_; 
v_sz_boxed_2078_ = lean_unbox_usize(v_sz_2074_);
lean_dec(v_sz_2074_);
v_i_boxed_2079_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2072_, v_as_2073_, v_sz_boxed_2078_, v_i_boxed_2079_, v_b_2076_);
lean_dec_ref(v_as_2073_);
lean_dec_ref(v___x_2072_);
return v_res_2080_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2083_; size_t v_sz_2084_; 
v___x_2083_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2084_ = lean_array_size(v___x_2083_);
return v_sz_2084_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2086_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
lean_ctor_set(v___x_2086_, 2, v___x_2085_);
lean_ctor_set(v___x_2086_, 3, v___x_2085_);
lean_ctor_set(v___x_2086_, 4, v___x_2085_);
lean_ctor_set(v___x_2086_, 5, v___x_2085_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2095_ = l_Lean_Name_append(v___x_2094_, v___x_2093_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2098_ = l_Lean_stringToMessageData(v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_options_2105_; lean_object* v_inheritedTraceOptions_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; size_t v_sz_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v_options_2105_ = lean_ctor_get(v_a_2102_, 2);
v_inheritedTraceOptions_2106_ = lean_ctor_get(v_a_2102_, 13);
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2108_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2109_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2110_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2105_, v___x_2109_, v_sz_2110_, v___x_2111_, v___x_2108_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2172_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2172_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2172_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = lean_array_get_size(v_a_2113_);
v___x_2161_ = lean_nat_dec_eq(v___x_2160_, v___x_2107_);
if (v___x_2161_ == 0)
{
uint8_t v_hasTrace_2162_; 
v_hasTrace_2162_ = lean_ctor_get_uint8(v_options_2105_, sizeof(void*)*1);
if (v_hasTrace_2162_ == 0)
{
v___y_2118_ = v_a_2101_;
v___y_2119_ = v_a_2103_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2164_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2165_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2106_, v_options_2105_, v___x_2164_);
if (v___x_2165_ == 0)
{
v___y_2118_ = v_a_2101_;
v___y_2119_ = v_a_2103_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2166_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2099_);
v___x_2167_ = l_Lean_MessageData_ofName(v_declName_2099_);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2163_, v___x_2168_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_dec_ref_known(v___x_2169_, 1);
v___y_2118_ = v_a_2101_;
v___y_2119_ = v_a_2103_;
goto v___jp_2117_;
}
else
{
lean_del_object(v___x_2115_);
lean_dec(v_a_2113_);
lean_dec(v_declName_2099_);
return v___x_2169_;
}
}
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_del_object(v___x_2115_);
lean_dec(v_a_2113_);
lean_dec(v_declName_2099_);
v___x_2170_ = lean_box(0);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
v___jp_2117_:
{
lean_object* v___x_2120_; lean_object* v_env_2121_; lean_object* v_nextMacroScope_2122_; lean_object* v_ngen_2123_; lean_object* v_auxDeclNGen_2124_; lean_object* v_traceState_2125_; lean_object* v_messages_2126_; lean_object* v_infoState_2127_; lean_object* v_snapshotTasks_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2158_; 
v___x_2120_ = lean_st_ref_take(v___y_2119_);
v_env_2121_ = lean_ctor_get(v___x_2120_, 0);
v_nextMacroScope_2122_ = lean_ctor_get(v___x_2120_, 1);
v_ngen_2123_ = lean_ctor_get(v___x_2120_, 2);
v_auxDeclNGen_2124_ = lean_ctor_get(v___x_2120_, 3);
v_traceState_2125_ = lean_ctor_get(v___x_2120_, 4);
v_messages_2126_ = lean_ctor_get(v___x_2120_, 6);
v_infoState_2127_ = lean_ctor_get(v___x_2120_, 7);
v_snapshotTasks_2128_ = lean_ctor_get(v___x_2120_, 8);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v___x_2120_, 5);
lean_dec(v_unused_2159_);
v___x_2130_ = v___x_2120_;
v_isShared_2131_ = v_isSharedCheck_2158_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_snapshotTasks_2128_);
lean_inc(v_infoState_2127_);
lean_inc(v_messages_2126_);
lean_inc(v_traceState_2125_);
lean_inc(v_auxDeclNGen_2124_);
lean_inc(v_ngen_2123_);
lean_inc(v_nextMacroScope_2122_);
lean_inc(v_env_2121_);
lean_dec(v___x_2120_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2158_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2132_ = l_Lean_Meta_eqnOptionsExt;
v___x_2133_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2132_, v_env_2121_, v_declName_2099_, v_a_2113_);
v___x_2134_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 5, v___x_2134_);
lean_ctor_set(v___x_2130_, 0, v___x_2133_);
v___x_2136_ = v___x_2130_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_nextMacroScope_2122_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_ngen_2123_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_auxDeclNGen_2124_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_traceState_2125_);
lean_ctor_set(v_reuseFailAlloc_2157_, 5, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2157_, 6, v_messages_2126_);
lean_ctor_set(v_reuseFailAlloc_2157_, 7, v_infoState_2127_);
lean_ctor_set(v_reuseFailAlloc_2157_, 8, v_snapshotTasks_2128_);
v___x_2136_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_mctx_2139_; lean_object* v_zetaDeltaFVarIds_2140_; lean_object* v_postponed_2141_; lean_object* v_diag_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2155_; 
v___x_2137_ = lean_st_ref_set(v___y_2119_, v___x_2136_);
v___x_2138_ = lean_st_ref_take(v___y_2118_);
v_mctx_2139_ = lean_ctor_get(v___x_2138_, 0);
v_zetaDeltaFVarIds_2140_ = lean_ctor_get(v___x_2138_, 2);
v_postponed_2141_ = lean_ctor_get(v___x_2138_, 3);
v_diag_2142_ = lean_ctor_get(v___x_2138_, 4);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v___x_2138_, 1);
lean_dec(v_unused_2156_);
v___x_2144_ = v___x_2138_;
v_isShared_2145_ = v_isSharedCheck_2155_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_diag_2142_);
lean_inc(v_postponed_2141_);
lean_inc(v_zetaDeltaFVarIds_2140_);
lean_inc(v_mctx_2139_);
lean_dec(v___x_2138_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2155_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v___x_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_mctx_2139_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_zetaDeltaFVarIds_2140_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_postponed_2141_);
lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_diag_2142_);
v___x_2148_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2149_ = lean_st_ref_set(v___y_2118_, v___x_2148_);
v___x_2150_ = lean_box(0);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2150_);
v___x_2152_ = v___x_2115_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
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
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_declName_2099_);
v_a_2173_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2112_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2112_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2188_, lean_object* v_as_2189_, size_t v_sz_2190_, size_t v_i_2191_, lean_object* v_b_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2188_, v_as_2189_, v_sz_2190_, v_i_2191_, v_b_2192_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2199_, lean_object* v_as_2200_, lean_object* v_sz_2201_, lean_object* v_i_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
size_t v_sz_boxed_2209_; size_t v_i_boxed_2210_; lean_object* v_res_2211_; 
v_sz_boxed_2209_ = lean_unbox_usize(v_sz_2201_);
lean_dec(v_sz_2201_);
v_i_boxed_2210_ = lean_unbox_usize(v_i_2202_);
lean_dec(v_i_2202_);
v_res_2211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2199_, v_as_2200_, v_sz_boxed_2209_, v_i_boxed_2210_, v_b_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_as_2200_);
lean_dec_ref(v___x_2199_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_st_mk_ref(v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2237_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2237_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2237_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_unbox(v_a_2221_);
lean_dec(v_a_2221_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
lean_dec_ref(v_f_2218_);
v___x_2226_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2226_);
v___x_2228_ = v___x_2223_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2230_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2231_ = lean_st_ref_take(v___x_2230_);
v___x_2232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2232_, 0, v_f_2218_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = lean_st_ref_set(v___x_2230_, v___x_2232_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2233_);
v___x_2235_ = v___x_2223_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_f_2218_);
v_a_2238_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2220_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2220_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2252_, lean_object* v_as_x27_2253_, lean_object* v_b_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
if (lean_obj_tag(v_as_x27_2253_) == 0)
{
lean_object* v___x_2260_; 
lean_dec(v_declName_2252_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_b_2254_);
return v___x_2260_;
}
else
{
lean_object* v_head_2261_; lean_object* v_tail_2262_; lean_object* v___x_2263_; 
lean_dec_ref(v_b_2254_);
v_head_2261_ = lean_ctor_get(v_as_x27_2253_, 0);
v_tail_2262_ = lean_ctor_get(v_as_x27_2253_, 1);
lean_inc(v_head_2261_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v_declName_2252_);
v___x_2263_ = lean_apply_6(v_head_2261_, v_declName_2252_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, lean_box(0));
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2276_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2276_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2276_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_box(0);
if (lean_obj_tag(v_a_2264_) == 1)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_dec(v_declName_2252_);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_a_2264_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v___x_2268_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2270_);
v___x_2272_ = v___x_2266_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
else
{
lean_object* v___x_2274_; 
lean_del_object(v___x_2266_);
lean_dec(v_a_2264_);
v___x_2274_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2253_ = v_tail_2262_;
v_b_2254_ = v___x_2274_;
goto _start;
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_declName_2252_);
v_a_2277_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2263_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2263_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2285_, lean_object* v_as_x27_2286_, lean_object* v_b_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2285_, v_as_x27_2286_, v_b_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v_as_x27_2286_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2294_, lean_object* v_declName_2295_, uint8_t v_nonRec_2296_, lean_object* v___x_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2306_; lean_object* v_env_2307_; uint8_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2306_ = lean_st_ref_get(v___y_2301_);
v_env_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc_ref(v_env_2307_);
lean_dec(v___x_2306_);
v___x_2308_ = 1;
lean_inc(v___x_2294_);
v___x_2309_ = l_Lean_Environment_contains(v_env_2307_, v___x_2294_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; 
lean_dec(v___x_2294_);
lean_inc(v_declName_2295_);
v___x_2310_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2295_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; uint8_t v___x_2312_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = lean_unbox(v_a_2311_);
lean_dec(v_a_2311_);
if (v___x_2312_ == 0)
{
lean_dec_ref(v___x_2297_);
lean_dec(v_declName_2295_);
goto v___jp_2303_;
}
else
{
lean_object* v___x_2313_; 
lean_inc(v_declName_2295_);
v___x_2313_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2295_, v___y_2301_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; uint8_t v___x_2315_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = lean_unbox(v_a_2314_);
lean_dec(v_a_2314_);
if (v___x_2315_ == 0)
{
if (v_nonRec_2296_ == 0)
{
lean_dec_ref(v___x_2297_);
lean_dec(v_declName_2295_);
goto v___jp_2303_;
}
else
{
lean_object* v___x_2316_; lean_object* v_env_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2316_ = lean_st_ref_get(v___y_2301_);
v_env_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc_ref(v_env_2317_);
lean_dec(v___x_2316_);
lean_inc(v_declName_2295_);
v___x_2318_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2317_, v_declName_2295_, v___x_2297_);
v___x_2319_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2295_, v___x_2318_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
return v___x_2319_;
}
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v___x_2297_);
v___x_2320_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2321_ = lean_st_ref_get(v___x_2320_);
v___x_2322_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2323_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2295_, v___x_2321_, v___x_2322_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___x_2321_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2333_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_fst_2328_; 
v_fst_2328_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_fst_2328_);
lean_dec(v_a_2324_);
if (lean_obj_tag(v_fst_2328_) == 0)
{
lean_del_object(v___x_2326_);
goto v___jp_2303_;
}
else
{
lean_object* v_val_2329_; lean_object* v___x_2331_; 
v_val_2329_ = lean_ctor_get(v_fst_2328_, 0);
lean_inc(v_val_2329_);
lean_dec_ref_known(v_fst_2328_, 1);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v_val_2329_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_val_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2323_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2323_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v___x_2297_);
lean_dec(v_declName_2295_);
v_a_2342_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2313_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2313_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v___x_2297_);
lean_dec(v_declName_2295_);
v_a_2350_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2310_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2310_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec_ref(v___x_2297_);
lean_dec(v_declName_2295_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2294_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
v___jp_2303_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_box(0);
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2360_, lean_object* v_declName_2361_, lean_object* v_nonRec_2362_, lean_object* v___x_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v_nonRec_boxed_2369_; lean_object* v_res_2370_; 
v_nonRec_boxed_2369_ = lean_unbox(v_nonRec_2362_);
v_res_2370_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2360_, v_declName_2361_, v_nonRec_boxed_2369_, v___x_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_ref_2377_; lean_object* v___x_2378_; lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2387_; 
v_ref_2377_ = lean_ctor_get(v___y_2374_, 5);
v___x_2378_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
lean_inc(v_ref_2377_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_ref_2377_);
lean_ctor_set(v___x_2383_, 1, v_a_2379_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 1);
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2395_, uint8_t v_isExporting_2396_, lean_object* v___x_2397_, lean_object* v___y_2398_, lean_object* v___x_2399_, lean_object* v_a_x3f_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v_env_2403_; lean_object* v_nextMacroScope_2404_; lean_object* v_ngen_2405_; lean_object* v_auxDeclNGen_2406_; lean_object* v_traceState_2407_; lean_object* v_messages_2408_; lean_object* v_infoState_2409_; lean_object* v_snapshotTasks_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2435_; 
v___x_2402_ = lean_st_ref_take(v___y_2395_);
v_env_2403_ = lean_ctor_get(v___x_2402_, 0);
v_nextMacroScope_2404_ = lean_ctor_get(v___x_2402_, 1);
v_ngen_2405_ = lean_ctor_get(v___x_2402_, 2);
v_auxDeclNGen_2406_ = lean_ctor_get(v___x_2402_, 3);
v_traceState_2407_ = lean_ctor_get(v___x_2402_, 4);
v_messages_2408_ = lean_ctor_get(v___x_2402_, 6);
v_infoState_2409_ = lean_ctor_get(v___x_2402_, 7);
v_snapshotTasks_2410_ = lean_ctor_get(v___x_2402_, 8);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; 
v_unused_2436_ = lean_ctor_get(v___x_2402_, 5);
lean_dec(v_unused_2436_);
v___x_2412_ = v___x_2402_;
v_isShared_2413_ = v_isSharedCheck_2435_;
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
v_isShared_2413_ = v_isSharedCheck_2435_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = l_Lean_Environment_setExporting(v_env_2403_, v_isExporting_2396_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 5, v___x_2397_);
lean_ctor_set(v___x_2412_, 0, v___x_2414_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_nextMacroScope_2404_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_ngen_2405_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v_auxDeclNGen_2406_);
lean_ctor_set(v_reuseFailAlloc_2434_, 4, v_traceState_2407_);
lean_ctor_set(v_reuseFailAlloc_2434_, 5, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2434_, 6, v_messages_2408_);
lean_ctor_set(v_reuseFailAlloc_2434_, 7, v_infoState_2409_);
lean_ctor_set(v_reuseFailAlloc_2434_, 8, v_snapshotTasks_2410_);
v___x_2416_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v_mctx_2419_; lean_object* v_zetaDeltaFVarIds_2420_; lean_object* v_postponed_2421_; lean_object* v_diag_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2432_; 
v___x_2417_ = lean_st_ref_set(v___y_2395_, v___x_2416_);
v___x_2418_ = lean_st_ref_take(v___y_2398_);
v_mctx_2419_ = lean_ctor_get(v___x_2418_, 0);
v_zetaDeltaFVarIds_2420_ = lean_ctor_get(v___x_2418_, 2);
v_postponed_2421_ = lean_ctor_get(v___x_2418_, 3);
v_diag_2422_ = lean_ctor_get(v___x_2418_, 4);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2418_, 1);
lean_dec(v_unused_2433_);
v___x_2424_ = v___x_2418_;
v_isShared_2425_ = v_isSharedCheck_2432_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_diag_2422_);
lean_inc(v_postponed_2421_);
lean_inc(v_zetaDeltaFVarIds_2420_);
lean_inc(v_mctx_2419_);
lean_dec(v___x_2418_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2432_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2399_);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_mctx_2419_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_zetaDeltaFVarIds_2420_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_postponed_2421_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_diag_2422_);
v___x_2427_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = lean_st_ref_set(v___y_2398_, v___x_2427_);
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2437_, lean_object* v_isExporting_2438_, lean_object* v___x_2439_, lean_object* v___y_2440_, lean_object* v___x_2441_, lean_object* v_a_x3f_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v_isExporting_boxed_2444_; lean_object* v_res_2445_; 
v_isExporting_boxed_2444_ = lean_unbox(v_isExporting_2438_);
v_res_2445_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2437_, v_isExporting_boxed_2444_, v___x_2439_, v___y_2440_, v___x_2441_, v_a_x3f_2442_);
lean_dec(v_a_x3f_2442_);
lean_dec(v___y_2440_);
lean_dec(v___y_2437_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2446_, uint8_t v_isExporting_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; lean_object* v_env_2454_; uint8_t v_isExporting_2455_; uint8_t v___y_2522_; lean_object* v___x_2524_; uint8_t v_isModule_2525_; uint8_t v___x_2526_; 
v___x_2453_ = lean_st_ref_get(v___y_2451_);
v_env_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_ref(v_env_2454_);
lean_dec(v___x_2453_);
v_isExporting_2455_ = lean_ctor_get_uint8(v_env_2454_, sizeof(void*)*8);
v___x_2524_ = l_Lean_Environment_header(v_env_2454_);
lean_dec_ref(v_env_2454_);
v_isModule_2525_ = lean_ctor_get_uint8(v___x_2524_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2524_);
v___x_2526_ = lean_bool_not(v_isModule_2525_);
if (v___x_2526_ == 0)
{
if (v_isExporting_2455_ == 0)
{
if (v_isExporting_2447_ == 0)
{
lean_object* v___x_2527_; 
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
v___x_2527_ = lean_apply_5(v_x_2446_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
return v___x_2527_;
}
else
{
goto v___jp_2456_;
}
}
else
{
v___y_2522_ = v_isExporting_2447_;
goto v___jp_2521_;
}
}
else
{
v___y_2522_ = v___x_2526_;
goto v___jp_2521_;
}
v___jp_2456_:
{
lean_object* v___x_2457_; lean_object* v_env_2458_; lean_object* v_nextMacroScope_2459_; lean_object* v_ngen_2460_; lean_object* v_auxDeclNGen_2461_; lean_object* v_traceState_2462_; lean_object* v_messages_2463_; lean_object* v_infoState_2464_; lean_object* v_snapshotTasks_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2519_; 
v___x_2457_ = lean_st_ref_take(v___y_2451_);
v_env_2458_ = lean_ctor_get(v___x_2457_, 0);
v_nextMacroScope_2459_ = lean_ctor_get(v___x_2457_, 1);
v_ngen_2460_ = lean_ctor_get(v___x_2457_, 2);
v_auxDeclNGen_2461_ = lean_ctor_get(v___x_2457_, 3);
v_traceState_2462_ = lean_ctor_get(v___x_2457_, 4);
v_messages_2463_ = lean_ctor_get(v___x_2457_, 6);
v_infoState_2464_ = lean_ctor_get(v___x_2457_, 7);
v_snapshotTasks_2465_ = lean_ctor_get(v___x_2457_, 8);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v___x_2457_, 5);
lean_dec(v_unused_2520_);
v___x_2467_ = v___x_2457_;
v_isShared_2468_ = v_isSharedCheck_2519_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snapshotTasks_2465_);
lean_inc(v_infoState_2464_);
lean_inc(v_messages_2463_);
lean_inc(v_traceState_2462_);
lean_inc(v_auxDeclNGen_2461_);
lean_inc(v_ngen_2460_);
lean_inc(v_nextMacroScope_2459_);
lean_inc(v_env_2458_);
lean_dec(v___x_2457_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2519_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2469_ = l_Lean_Environment_setExporting(v_env_2458_, v_isExporting_2447_);
v___x_2470_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 5, v___x_2470_);
lean_ctor_set(v___x_2467_, 0, v___x_2469_);
v___x_2472_ = v___x_2467_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_nextMacroScope_2459_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_ngen_2460_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_auxDeclNGen_2461_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_traceState_2462_);
lean_ctor_set(v_reuseFailAlloc_2518_, 5, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2518_, 6, v_messages_2463_);
lean_ctor_set(v_reuseFailAlloc_2518_, 7, v_infoState_2464_);
lean_ctor_set(v_reuseFailAlloc_2518_, 8, v_snapshotTasks_2465_);
v___x_2472_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_mctx_2475_; lean_object* v_zetaDeltaFVarIds_2476_; lean_object* v_postponed_2477_; lean_object* v_diag_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2516_; 
v___x_2473_ = lean_st_ref_set(v___y_2451_, v___x_2472_);
v___x_2474_ = lean_st_ref_take(v___y_2449_);
v_mctx_2475_ = lean_ctor_get(v___x_2474_, 0);
v_zetaDeltaFVarIds_2476_ = lean_ctor_get(v___x_2474_, 2);
v_postponed_2477_ = lean_ctor_get(v___x_2474_, 3);
v_diag_2478_ = lean_ctor_get(v___x_2474_, 4);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v___x_2474_, 1);
lean_dec(v_unused_2517_);
v___x_2480_ = v___x_2474_;
v_isShared_2481_ = v_isSharedCheck_2516_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_diag_2478_);
lean_inc(v_postponed_2477_);
lean_inc(v_zetaDeltaFVarIds_2476_);
lean_inc(v_mctx_2475_);
lean_dec(v___x_2474_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2516_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v___x_2482_);
v___x_2484_ = v___x_2480_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_mctx_2475_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_zetaDeltaFVarIds_2476_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_postponed_2477_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_diag_2478_);
v___x_2484_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; lean_object* v_r_2486_; 
v___x_2485_ = lean_st_ref_set(v___y_2449_, v___x_2484_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
v_r_2486_ = lean_apply_5(v_x_2446_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
if (lean_obj_tag(v_r_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2503_; 
v_a_2487_ = lean_ctor_get(v_r_2486_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_r_2486_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2489_ = v_r_2486_;
v_isShared_2490_ = v_isSharedCheck_2503_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v_r_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2503_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
lean_inc(v_a_2487_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set_tag(v___x_2489_, 1);
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
v___x_2493_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2451_, v_isExporting_2455_, v___x_2470_, v___y_2449_, v___x_2482_, v___x_2492_);
lean_dec_ref(v___x_2492_);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v___x_2493_, 0);
lean_dec(v_unused_2501_);
v___x_2495_ = v___x_2493_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_dec(v___x_2493_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v_a_2487_);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2487_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
v_a_2504_ = lean_ctor_get(v_r_2486_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v_r_2486_, 1);
v___x_2505_ = lean_box(0);
v___x_2506_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2451_, v_isExporting_2455_, v___x_2470_, v___y_2449_, v___x_2482_, v___x_2505_);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v___x_2506_, 0);
lean_dec(v_unused_2514_);
v___x_2508_ = v___x_2506_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_dec(v___x_2506_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set_tag(v___x_2508_, 1);
lean_ctor_set(v___x_2508_, 0, v_a_2504_);
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2504_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
}
}
}
v___jp_2521_:
{
if (v___y_2522_ == 0)
{
goto v___jp_2456_;
}
else
{
lean_object* v___x_2523_; 
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
v___x_2523_ = lean_apply_5(v_x_2446_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
return v___x_2523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2528_, lean_object* v_isExporting_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
uint8_t v_isExporting_boxed_2535_; lean_object* v_res_2536_; 
v_isExporting_boxed_2535_ = lean_unbox(v_isExporting_2529_);
v_res_2536_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2528_, v_isExporting_boxed_2535_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2537_, uint8_t v_when_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
if (v_when_2538_ == 0)
{
lean_object* v___x_2544_; 
lean_inc(v___y_2542_);
lean_inc_ref(v___y_2541_);
lean_inc(v___y_2540_);
lean_inc_ref(v___y_2539_);
v___x_2544_ = lean_apply_5(v_x_2537_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, lean_box(0));
return v___x_2544_;
}
else
{
uint8_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = 0;
v___x_2546_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2537_, v___x_2545_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2547_, lean_object* v_when_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
uint8_t v_when_boxed_2554_; lean_object* v_res_2555_; 
v_when_boxed_2554_ = lean_unbox(v_when_2548_);
v_res_2555_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2547_, v_when_boxed_2554_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
return v_res_2555_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2558_ = l_Lean_stringToMessageData(v___x_2557_);
return v___x_2558_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
return v___x_2561_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2564_ = l_Lean_stringToMessageData(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2565_, uint8_t v_nonRec_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; lean_object* v_env_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; 
v___x_2572_ = lean_st_ref_get(v___y_2570_);
v_env_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc_ref(v_env_2573_);
lean_dec(v___x_2572_);
v___x_2574_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2565_);
v___x_2575_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2573_, v_declName_2565_, v___x_2574_);
v___x_2576_ = lean_box(v_nonRec_2566_);
lean_inc(v___x_2575_);
v___f_2577_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2577_, 0, v___x_2575_);
lean_closure_set(v___f_2577_, 1, v_declName_2565_);
lean_closure_set(v___f_2577_, 2, v___x_2576_);
lean_closure_set(v___f_2577_, 3, v___x_2574_);
v___x_2578_ = 1;
v___x_2579_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2577_, v___x_2578_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
if (lean_obj_tag(v_a_2580_) == 1)
{
lean_object* v_val_2581_; uint8_t v___x_2582_; 
v_val_2581_ = lean_ctor_get(v_a_2580_, 0);
lean_inc(v_val_2581_);
lean_dec_ref_known(v_a_2580_, 1);
v___x_2582_ = lean_name_eq(v_val_2581_, v___x_2575_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref_known(v___x_2579_, 1);
v___x_2583_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2584_ = l_Lean_MessageData_ofName(v_val_2581_);
v___x_2585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = l_Lean_MessageData_ofName(v___x_2575_);
v___x_2589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2591_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
else
{
lean_dec(v_val_2581_);
lean_dec(v___x_2575_);
return v___x_2579_;
}
}
else
{
lean_dec(v_a_2580_);
lean_dec(v___x_2575_);
return v___x_2579_;
}
}
else
{
lean_dec(v___x_2575_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2601_, lean_object* v_nonRec_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
uint8_t v_nonRec_boxed_2608_; lean_object* v_res_2609_; 
v_nonRec_boxed_2608_ = lean_unbox(v_nonRec_2602_);
v_res_2609_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2601_, v_nonRec_boxed_2608_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2610_, uint8_t v_nonRec_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2617_ = lean_box(v_nonRec_2611_);
v___f_2618_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2618_, 0, v_declName_2610_);
lean_closure_set(v___f_2618_, 1, v___x_2617_);
v___x_2619_ = lean_unsigned_to_nat(32u);
v___x_2620_ = lean_mk_empty_array_with_capacity(v___x_2619_);
lean_dec_ref(v___x_2620_);
v___x_2621_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2622_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2623_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2621_, v___x_2622_, v___f_2618_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2624_, lean_object* v_nonRec_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
uint8_t v_nonRec_boxed_2631_; lean_object* v_res_2632_; 
v_nonRec_boxed_2631_ = lean_unbox(v_nonRec_2625_);
v_res_2632_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2624_, v_nonRec_boxed_2631_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2633_, lean_object* v_as_2634_, lean_object* v_as_x27_2635_, lean_object* v_b_2636_, lean_object* v_a_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2633_, v_as_x27_2635_, v_b_2636_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2644_, lean_object* v_as_2645_, lean_object* v_as_x27_2646_, lean_object* v_b_2647_, lean_object* v_a_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2644_, v_as_2645_, v_as_x27_2646_, v_b_2647_, v_a_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v_as_x27_2646_);
lean_dec(v_as_2645_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2655_, lean_object* v_x_2656_, uint8_t v_isExporting_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2656_, v_isExporting_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2664_, lean_object* v_x_2665_, lean_object* v_isExporting_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v_isExporting_boxed_2672_; lean_object* v_res_2673_; 
v_isExporting_boxed_2672_ = lean_unbox(v_isExporting_2666_);
v_res_2673_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2664_, v_x_2665_, v_isExporting_boxed_2672_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2674_, lean_object* v_x_2675_, uint8_t v_when_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2675_, v_when_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2683_, lean_object* v_x_2684_, lean_object* v_when_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_when_boxed_2691_; lean_object* v_res_2692_; 
v_when_boxed_2691_ = lean_unbox(v_when_2685_);
v_res_2692_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2683_, v_x_2684_, v_when_boxed_2691_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2701_, v_msg_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2708_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_unsigned_to_nat(32u);
v___x_2710_ = lean_mk_empty_array_with_capacity(v___x_2709_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2712_ = ((size_t)5ULL);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = lean_unsigned_to_nat(32u);
v___x_2715_ = lean_mk_empty_array_with_capacity(v___x_2714_);
v___x_2716_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2717_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2715_);
lean_ctor_set(v___x_2717_, 2, v___x_2713_);
lean_ctor_set(v___x_2717_, 3, v___x_2713_);
lean_ctor_set_usize(v___x_2717_, 4, v___x_2712_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; lean_object* v_traceState_2721_; lean_object* v_traces_2722_; lean_object* v___x_2723_; lean_object* v_traceState_2724_; lean_object* v_env_2725_; lean_object* v_nextMacroScope_2726_; lean_object* v_ngen_2727_; lean_object* v_auxDeclNGen_2728_; lean_object* v_cache_2729_; lean_object* v_messages_2730_; lean_object* v_infoState_2731_; lean_object* v_snapshotTasks_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2751_; 
v___x_2720_ = lean_st_ref_get(v___y_2718_);
v_traceState_2721_ = lean_ctor_get(v___x_2720_, 4);
lean_inc_ref(v_traceState_2721_);
lean_dec(v___x_2720_);
v_traces_2722_ = lean_ctor_get(v_traceState_2721_, 0);
lean_inc_ref(v_traces_2722_);
lean_dec_ref(v_traceState_2721_);
v___x_2723_ = lean_st_ref_take(v___y_2718_);
v_traceState_2724_ = lean_ctor_get(v___x_2723_, 4);
v_env_2725_ = lean_ctor_get(v___x_2723_, 0);
v_nextMacroScope_2726_ = lean_ctor_get(v___x_2723_, 1);
v_ngen_2727_ = lean_ctor_get(v___x_2723_, 2);
v_auxDeclNGen_2728_ = lean_ctor_get(v___x_2723_, 3);
v_cache_2729_ = lean_ctor_get(v___x_2723_, 5);
v_messages_2730_ = lean_ctor_get(v___x_2723_, 6);
v_infoState_2731_ = lean_ctor_get(v___x_2723_, 7);
v_snapshotTasks_2732_ = lean_ctor_get(v___x_2723_, 8);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2734_ = v___x_2723_;
v_isShared_2735_ = v_isSharedCheck_2751_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_snapshotTasks_2732_);
lean_inc(v_infoState_2731_);
lean_inc(v_messages_2730_);
lean_inc(v_cache_2729_);
lean_inc(v_traceState_2724_);
lean_inc(v_auxDeclNGen_2728_);
lean_inc(v_ngen_2727_);
lean_inc(v_nextMacroScope_2726_);
lean_inc(v_env_2725_);
lean_dec(v___x_2723_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2751_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
uint64_t v_tid_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2749_; 
v_tid_2736_ = lean_ctor_get_uint64(v_traceState_2724_, sizeof(void*)*1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_traceState_2724_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; 
v_unused_2750_ = lean_ctor_get(v_traceState_2724_, 0);
lean_dec(v_unused_2750_);
v___x_2738_ = v_traceState_2724_;
v_isShared_2739_ = v_isSharedCheck_2749_;
goto v_resetjp_2737_;
}
else
{
lean_dec(v_traceState_2724_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2749_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2740_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2740_);
lean_ctor_set_uint64(v_reuseFailAlloc_2748_, sizeof(void*)*1, v_tid_2736_);
v___x_2742_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2744_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v___x_2742_);
v___x_2744_ = v___x_2734_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_env_2725_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_nextMacroScope_2726_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_ngen_2727_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_auxDeclNGen_2728_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2747_, 5, v_cache_2729_);
lean_ctor_set(v_reuseFailAlloc_2747_, 6, v_messages_2730_);
lean_ctor_set(v_reuseFailAlloc_2747_, 7, v_infoState_2731_);
lean_ctor_set(v_reuseFailAlloc_2747_, 8, v_snapshotTasks_2732_);
v___x_2744_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = lean_st_ref_set(v___y_2718_, v___x_2744_);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v_traces_2722_);
return v___x_2746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2752_);
lean_dec(v___y_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
return v_res_2762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2766_, lean_object* v_x_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2771_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2772_ = l_Lean_MessageData_ofName(v_name_2766_);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2775_, lean_object* v_x_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2775_, v_x_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec_ref(v_x_2776_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2781_){
_start:
{
if (lean_obj_tag(v_x_2781_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_a_2783_ = lean_ctor_get(v_x_2781_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_x_2781_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v_x_2781_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v_x_2781_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set_tag(v___x_2785_, 1);
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
v_a_2791_ = lean_ctor_get(v_x_2781_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_x_2781_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v_x_2781_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v_x_2781_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set_tag(v___x_2793_, 0);
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2799_);
return v_res_2801_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2802_){
_start:
{
if (lean_obj_tag(v_e_2802_) == 0)
{
uint8_t v___x_2803_; 
v___x_2803_ = 2;
return v___x_2803_;
}
else
{
lean_object* v_a_2804_; uint8_t v___x_2805_; 
v_a_2804_ = lean_ctor_get(v_e_2802_, 0);
v___x_2805_ = lean_unbox(v_a_2804_);
if (v___x_2805_ == 0)
{
uint8_t v___x_2806_; 
v___x_2806_ = 1;
return v___x_2806_;
}
else
{
uint8_t v___x_2807_; 
v___x_2807_ = 0;
return v___x_2807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2808_){
_start:
{
uint8_t v_res_2809_; lean_object* v_r_2810_; 
v_res_2809_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2808_);
lean_dec_ref(v_e_2808_);
v_r_2810_ = lean_box(v_res_2809_);
return v_r_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2811_, size_t v_i_2812_, lean_object* v_bs_2813_){
_start:
{
uint8_t v___x_2814_; 
v___x_2814_ = lean_usize_dec_lt(v_i_2812_, v_sz_2811_);
if (v___x_2814_ == 0)
{
return v_bs_2813_;
}
else
{
lean_object* v_v_2815_; lean_object* v_msg_2816_; lean_object* v___x_2817_; lean_object* v_bs_x27_2818_; size_t v___x_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v_v_2815_ = lean_array_uget_borrowed(v_bs_2813_, v_i_2812_);
v_msg_2816_ = lean_ctor_get(v_v_2815_, 1);
lean_inc_ref(v_msg_2816_);
v___x_2817_ = lean_unsigned_to_nat(0u);
v_bs_x27_2818_ = lean_array_uset(v_bs_2813_, v_i_2812_, v___x_2817_);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_add(v_i_2812_, v___x_2819_);
v___x_2821_ = lean_array_uset(v_bs_x27_2818_, v_i_2812_, v_msg_2816_);
v_i_2812_ = v___x_2820_;
v_bs_2813_ = v___x_2821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2823_, lean_object* v_i_2824_, lean_object* v_bs_2825_){
_start:
{
size_t v_sz_boxed_2826_; size_t v_i_boxed_2827_; lean_object* v_res_2828_; 
v_sz_boxed_2826_ = lean_unbox_usize(v_sz_2823_);
lean_dec(v_sz_2823_);
v_i_boxed_2827_ = lean_unbox_usize(v_i_2824_);
lean_dec(v_i_2824_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2826_, v_i_boxed_2827_, v_bs_2825_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2829_, lean_object* v_data_2830_, lean_object* v_ref_2831_, lean_object* v_msg_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_fileName_2836_; lean_object* v_fileMap_2837_; lean_object* v_options_2838_; lean_object* v_currRecDepth_2839_; lean_object* v_maxRecDepth_2840_; lean_object* v_ref_2841_; lean_object* v_currNamespace_2842_; lean_object* v_openDecls_2843_; lean_object* v_initHeartbeats_2844_; lean_object* v_maxHeartbeats_2845_; lean_object* v_quotContext_2846_; lean_object* v_currMacroScope_2847_; uint8_t v_diag_2848_; lean_object* v_cancelTk_x3f_2849_; uint8_t v_suppressElabErrors_2850_; lean_object* v_inheritedTraceOptions_2851_; lean_object* v___x_2852_; lean_object* v_traceState_2853_; lean_object* v_traces_2854_; lean_object* v_ref_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; size_t v_sz_2858_; size_t v___x_2859_; lean_object* v___x_2860_; lean_object* v_msg_2861_; lean_object* v___x_2862_; lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2900_; 
v_fileName_2836_ = lean_ctor_get(v___y_2833_, 0);
v_fileMap_2837_ = lean_ctor_get(v___y_2833_, 1);
v_options_2838_ = lean_ctor_get(v___y_2833_, 2);
v_currRecDepth_2839_ = lean_ctor_get(v___y_2833_, 3);
v_maxRecDepth_2840_ = lean_ctor_get(v___y_2833_, 4);
v_ref_2841_ = lean_ctor_get(v___y_2833_, 5);
v_currNamespace_2842_ = lean_ctor_get(v___y_2833_, 6);
v_openDecls_2843_ = lean_ctor_get(v___y_2833_, 7);
v_initHeartbeats_2844_ = lean_ctor_get(v___y_2833_, 8);
v_maxHeartbeats_2845_ = lean_ctor_get(v___y_2833_, 9);
v_quotContext_2846_ = lean_ctor_get(v___y_2833_, 10);
v_currMacroScope_2847_ = lean_ctor_get(v___y_2833_, 11);
v_diag_2848_ = lean_ctor_get_uint8(v___y_2833_, sizeof(void*)*14);
v_cancelTk_x3f_2849_ = lean_ctor_get(v___y_2833_, 12);
v_suppressElabErrors_2850_ = lean_ctor_get_uint8(v___y_2833_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2851_ = lean_ctor_get(v___y_2833_, 13);
v___x_2852_ = lean_st_ref_get(v___y_2834_);
v_traceState_2853_ = lean_ctor_get(v___x_2852_, 4);
lean_inc_ref(v_traceState_2853_);
lean_dec(v___x_2852_);
v_traces_2854_ = lean_ctor_get(v_traceState_2853_, 0);
lean_inc_ref(v_traces_2854_);
lean_dec_ref(v_traceState_2853_);
v_ref_2855_ = l_Lean_replaceRef(v_ref_2831_, v_ref_2841_);
lean_inc_ref(v_inheritedTraceOptions_2851_);
lean_inc(v_cancelTk_x3f_2849_);
lean_inc(v_currMacroScope_2847_);
lean_inc(v_quotContext_2846_);
lean_inc(v_maxHeartbeats_2845_);
lean_inc(v_initHeartbeats_2844_);
lean_inc(v_openDecls_2843_);
lean_inc(v_currNamespace_2842_);
lean_inc(v_maxRecDepth_2840_);
lean_inc(v_currRecDepth_2839_);
lean_inc_ref(v_options_2838_);
lean_inc_ref(v_fileMap_2837_);
lean_inc_ref(v_fileName_2836_);
v___x_2856_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2856_, 0, v_fileName_2836_);
lean_ctor_set(v___x_2856_, 1, v_fileMap_2837_);
lean_ctor_set(v___x_2856_, 2, v_options_2838_);
lean_ctor_set(v___x_2856_, 3, v_currRecDepth_2839_);
lean_ctor_set(v___x_2856_, 4, v_maxRecDepth_2840_);
lean_ctor_set(v___x_2856_, 5, v_ref_2855_);
lean_ctor_set(v___x_2856_, 6, v_currNamespace_2842_);
lean_ctor_set(v___x_2856_, 7, v_openDecls_2843_);
lean_ctor_set(v___x_2856_, 8, v_initHeartbeats_2844_);
lean_ctor_set(v___x_2856_, 9, v_maxHeartbeats_2845_);
lean_ctor_set(v___x_2856_, 10, v_quotContext_2846_);
lean_ctor_set(v___x_2856_, 11, v_currMacroScope_2847_);
lean_ctor_set(v___x_2856_, 12, v_cancelTk_x3f_2849_);
lean_ctor_set(v___x_2856_, 13, v_inheritedTraceOptions_2851_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*14, v_diag_2848_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*14 + 1, v_suppressElabErrors_2850_);
v___x_2857_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2854_);
lean_dec_ref(v_traces_2854_);
v_sz_2858_ = lean_array_size(v___x_2857_);
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2858_, v___x_2859_, v___x_2857_);
v_msg_2861_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2861_, 0, v_data_2830_);
lean_ctor_set(v_msg_2861_, 1, v_msg_2832_);
lean_ctor_set(v_msg_2861_, 2, v___x_2860_);
v___x_2862_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2861_, v___x_2856_, v___y_2834_);
lean_dec_ref_known(v___x_2856_, 14);
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2900_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2900_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v_traceState_2868_; lean_object* v_env_2869_; lean_object* v_nextMacroScope_2870_; lean_object* v_ngen_2871_; lean_object* v_auxDeclNGen_2872_; lean_object* v_cache_2873_; lean_object* v_messages_2874_; lean_object* v_infoState_2875_; lean_object* v_snapshotTasks_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2899_; 
v___x_2867_ = lean_st_ref_take(v___y_2834_);
v_traceState_2868_ = lean_ctor_get(v___x_2867_, 4);
v_env_2869_ = lean_ctor_get(v___x_2867_, 0);
v_nextMacroScope_2870_ = lean_ctor_get(v___x_2867_, 1);
v_ngen_2871_ = lean_ctor_get(v___x_2867_, 2);
v_auxDeclNGen_2872_ = lean_ctor_get(v___x_2867_, 3);
v_cache_2873_ = lean_ctor_get(v___x_2867_, 5);
v_messages_2874_ = lean_ctor_get(v___x_2867_, 6);
v_infoState_2875_ = lean_ctor_get(v___x_2867_, 7);
v_snapshotTasks_2876_ = lean_ctor_get(v___x_2867_, 8);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2878_ = v___x_2867_;
v_isShared_2879_ = v_isSharedCheck_2899_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_snapshotTasks_2876_);
lean_inc(v_infoState_2875_);
lean_inc(v_messages_2874_);
lean_inc(v_cache_2873_);
lean_inc(v_traceState_2868_);
lean_inc(v_auxDeclNGen_2872_);
lean_inc(v_ngen_2871_);
lean_inc(v_nextMacroScope_2870_);
lean_inc(v_env_2869_);
lean_dec(v___x_2867_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2899_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint64_t v_tid_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2897_; 
v_tid_2880_ = lean_ctor_get_uint64(v_traceState_2868_, sizeof(void*)*1);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_traceState_2868_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v_traceState_2868_, 0);
lean_dec(v_unused_2898_);
v___x_2882_ = v_traceState_2868_;
v_isShared_2883_ = v_isSharedCheck_2897_;
goto v_resetjp_2881_;
}
else
{
lean_dec(v_traceState_2868_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2897_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_ref_2831_);
lean_ctor_set(v___x_2884_, 1, v_a_2863_);
v___x_2885_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2829_, v___x_2884_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2885_);
v___x_2887_ = v___x_2882_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2885_);
lean_ctor_set_uint64(v_reuseFailAlloc_2896_, sizeof(void*)*1, v_tid_2880_);
v___x_2887_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2889_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 4, v___x_2887_);
v___x_2889_ = v___x_2878_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_env_2869_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_nextMacroScope_2870_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_ngen_2871_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v_auxDeclNGen_2872_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2895_, 5, v_cache_2873_);
lean_ctor_set(v_reuseFailAlloc_2895_, 6, v_messages_2874_);
lean_ctor_set(v_reuseFailAlloc_2895_, 7, v_infoState_2875_);
lean_ctor_set(v_reuseFailAlloc_2895_, 8, v_snapshotTasks_2876_);
v___x_2889_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2890_ = lean_st_ref_set(v___y_2834_, v___x_2889_);
v___x_2891_ = lean_box(0);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2891_);
v___x_2893_ = v___x_2865_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2901_, lean_object* v_data_2902_, lean_object* v_ref_2903_, lean_object* v_msg_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2901_, v_data_2902_, v_ref_2903_, v_msg_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2908_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2911_ = l_Lean_stringToMessageData(v___x_2910_);
return v___x_2911_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2912_; double v___x_2913_; 
v___x_2912_ = lean_unsigned_to_nat(1000u);
v___x_2913_ = lean_float_of_nat(v___x_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2914_, uint8_t v_collapsed_2915_, lean_object* v_tag_2916_, lean_object* v_opts_2917_, uint8_t v_clsEnabled_2918_, lean_object* v_oldTraces_2919_, lean_object* v_msg_2920_, lean_object* v_resStartStop_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_fst_2925_; lean_object* v_snd_2926_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v_data_2930_; lean_object* v_fst_2941_; lean_object* v_snd_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; lean_object* v___y_2946_; lean_object* v_a_2947_; uint8_t v___y_2962_; double v___y_2993_; 
v_fst_2925_ = lean_ctor_get(v_resStartStop_2921_, 0);
lean_inc(v_fst_2925_);
v_snd_2926_ = lean_ctor_get(v_resStartStop_2921_, 1);
lean_inc(v_snd_2926_);
lean_dec_ref(v_resStartStop_2921_);
v_fst_2941_ = lean_ctor_get(v_snd_2926_, 0);
lean_inc(v_fst_2941_);
v_snd_2942_ = lean_ctor_get(v_snd_2926_, 1);
lean_inc(v_snd_2942_);
lean_dec(v_snd_2926_);
v___x_2943_ = l_Lean_trace_profiler;
v___x_2944_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2917_, v___x_2943_);
if (v___x_2944_ == 0)
{
v___y_2962_ = v___x_2944_;
goto v___jp_2961_;
}
else
{
lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2999_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2917_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3001_; double v___x_3002_; double v___x_3003_; double v___x_3004_; 
v___x_3000_ = l_Lean_trace_profiler_threshold;
v___x_3001_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2917_, v___x_3000_);
v___x_3002_ = lean_float_of_nat(v___x_3001_);
v___x_3003_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3004_ = lean_float_div(v___x_3002_, v___x_3003_);
v___y_2993_ = v___x_3004_;
goto v___jp_2992_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; double v___x_3007_; 
v___x_3005_ = l_Lean_trace_profiler_threshold;
v___x_3006_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2917_, v___x_3005_);
v___x_3007_ = lean_float_of_nat(v___x_3006_);
v___y_2993_ = v___x_3007_;
goto v___jp_2992_;
}
}
v___jp_2927_:
{
lean_object* v___x_2931_; 
lean_inc(v___y_2929_);
v___x_2931_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2919_, v_data_2930_, v___y_2929_, v___y_2928_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v___x_2932_; 
lean_dec_ref_known(v___x_2931_, 1);
v___x_2932_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2925_);
return v___x_2932_;
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v_fst_2925_);
v_a_2933_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2931_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2931_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
v___jp_2945_:
{
uint8_t v_result_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; double v___x_2951_; lean_object* v_data_2952_; 
v_result_2948_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2925_);
v___x_2949_ = lean_box(v_result_2948_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
v___x_2951_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2916_);
lean_inc_ref(v___x_2950_);
lean_inc(v_cls_2914_);
v_data_2952_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2952_, 0, v_cls_2914_);
lean_ctor_set(v_data_2952_, 1, v___x_2950_);
lean_ctor_set(v_data_2952_, 2, v_tag_2916_);
lean_ctor_set_float(v_data_2952_, sizeof(void*)*3, v___x_2951_);
lean_ctor_set_float(v_data_2952_, sizeof(void*)*3 + 8, v___x_2951_);
lean_ctor_set_uint8(v_data_2952_, sizeof(void*)*3 + 16, v_collapsed_2915_);
if (v___x_2944_ == 0)
{
lean_dec_ref_known(v___x_2950_, 1);
lean_dec(v_snd_2942_);
lean_dec(v_fst_2941_);
lean_dec_ref(v_tag_2916_);
lean_dec(v_cls_2914_);
v___y_2928_ = v_a_2947_;
v___y_2929_ = v___y_2946_;
v_data_2930_ = v_data_2952_;
goto v___jp_2927_;
}
else
{
lean_object* v_data_2953_; double v___x_2954_; double v___x_2955_; 
lean_dec_ref_known(v_data_2952_, 3);
v_data_2953_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2953_, 0, v_cls_2914_);
lean_ctor_set(v_data_2953_, 1, v___x_2950_);
lean_ctor_set(v_data_2953_, 2, v_tag_2916_);
v___x_2954_ = lean_unbox_float(v_fst_2941_);
lean_dec(v_fst_2941_);
lean_ctor_set_float(v_data_2953_, sizeof(void*)*3, v___x_2954_);
v___x_2955_ = lean_unbox_float(v_snd_2942_);
lean_dec(v_snd_2942_);
lean_ctor_set_float(v_data_2953_, sizeof(void*)*3 + 8, v___x_2955_);
lean_ctor_set_uint8(v_data_2953_, sizeof(void*)*3 + 16, v_collapsed_2915_);
v___y_2928_ = v_a_2947_;
v___y_2929_ = v___y_2946_;
v_data_2930_ = v_data_2953_;
goto v___jp_2927_;
}
}
v___jp_2956_:
{
lean_object* v_ref_2957_; lean_object* v___x_2958_; 
v_ref_2957_ = lean_ctor_get(v___y_2922_, 5);
lean_inc(v___y_2923_);
lean_inc_ref(v___y_2922_);
lean_inc(v_fst_2925_);
v___x_2958_ = lean_apply_4(v_msg_2920_, v_fst_2925_, v___y_2922_, v___y_2923_, lean_box(0));
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___y_2946_ = v_ref_2957_;
v_a_2947_ = v_a_2959_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_2960_; 
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2946_ = v_ref_2957_;
v_a_2947_ = v___x_2960_;
goto v___jp_2945_;
}
}
v___jp_2961_:
{
if (v_clsEnabled_2918_ == 0)
{
if (v___y_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v_traceState_2964_; lean_object* v_env_2965_; lean_object* v_nextMacroScope_2966_; lean_object* v_ngen_2967_; lean_object* v_auxDeclNGen_2968_; lean_object* v_cache_2969_; lean_object* v_messages_2970_; lean_object* v_infoState_2971_; lean_object* v_snapshotTasks_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_snd_2942_);
lean_dec(v_fst_2941_);
lean_dec_ref(v_msg_2920_);
lean_dec_ref(v_tag_2916_);
lean_dec(v_cls_2914_);
v___x_2963_ = lean_st_ref_take(v___y_2923_);
v_traceState_2964_ = lean_ctor_get(v___x_2963_, 4);
v_env_2965_ = lean_ctor_get(v___x_2963_, 0);
v_nextMacroScope_2966_ = lean_ctor_get(v___x_2963_, 1);
v_ngen_2967_ = lean_ctor_get(v___x_2963_, 2);
v_auxDeclNGen_2968_ = lean_ctor_get(v___x_2963_, 3);
v_cache_2969_ = lean_ctor_get(v___x_2963_, 5);
v_messages_2970_ = lean_ctor_get(v___x_2963_, 6);
v_infoState_2971_ = lean_ctor_get(v___x_2963_, 7);
v_snapshotTasks_2972_ = lean_ctor_get(v___x_2963_, 8);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2974_ = v___x_2963_;
v_isShared_2975_ = v_isSharedCheck_2991_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_snapshotTasks_2972_);
lean_inc(v_infoState_2971_);
lean_inc(v_messages_2970_);
lean_inc(v_cache_2969_);
lean_inc(v_traceState_2964_);
lean_inc(v_auxDeclNGen_2968_);
lean_inc(v_ngen_2967_);
lean_inc(v_nextMacroScope_2966_);
lean_inc(v_env_2965_);
lean_dec(v___x_2963_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2991_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
uint64_t v_tid_2976_; lean_object* v_traces_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2990_; 
v_tid_2976_ = lean_ctor_get_uint64(v_traceState_2964_, sizeof(void*)*1);
v_traces_2977_ = lean_ctor_get(v_traceState_2964_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_traceState_2964_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2979_ = v_traceState_2964_;
v_isShared_2980_ = v_isSharedCheck_2990_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_traces_2977_);
lean_dec(v_traceState_2964_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2990_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2981_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2919_, v_traces_2977_);
lean_dec_ref(v_traces_2977_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_2981_);
v___x_2983_ = v___x_2979_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2981_);
lean_ctor_set_uint64(v_reuseFailAlloc_2989_, sizeof(void*)*1, v_tid_2976_);
v___x_2983_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2985_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 4, v___x_2983_);
v___x_2985_ = v___x_2974_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_env_2965_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_nextMacroScope_2966_);
lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_ngen_2967_);
lean_ctor_set(v_reuseFailAlloc_2988_, 3, v_auxDeclNGen_2968_);
lean_ctor_set(v_reuseFailAlloc_2988_, 4, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2988_, 5, v_cache_2969_);
lean_ctor_set(v_reuseFailAlloc_2988_, 6, v_messages_2970_);
lean_ctor_set(v_reuseFailAlloc_2988_, 7, v_infoState_2971_);
lean_ctor_set(v_reuseFailAlloc_2988_, 8, v_snapshotTasks_2972_);
v___x_2985_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_st_ref_set(v___y_2923_, v___x_2985_);
v___x_2987_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2925_);
return v___x_2987_;
}
}
}
}
}
else
{
goto v___jp_2956_;
}
}
else
{
goto v___jp_2956_;
}
}
v___jp_2992_:
{
double v___x_2994_; double v___x_2995_; double v___x_2996_; uint8_t v___x_2997_; 
v___x_2994_ = lean_unbox_float(v_snd_2942_);
v___x_2995_ = lean_unbox_float(v_fst_2941_);
v___x_2996_ = lean_float_sub(v___x_2994_, v___x_2995_);
v___x_2997_ = lean_float_decLt(v___y_2993_, v___x_2996_);
v___y_2962_ = v___x_2997_;
goto v___jp_2961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3008_, lean_object* v_collapsed_3009_, lean_object* v_tag_3010_, lean_object* v_opts_3011_, lean_object* v_clsEnabled_3012_, lean_object* v_oldTraces_3013_, lean_object* v_msg_3014_, lean_object* v_resStartStop_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
uint8_t v_collapsed_boxed_3019_; uint8_t v_clsEnabled_boxed_3020_; lean_object* v_res_3021_; 
v_collapsed_boxed_3019_ = lean_unbox(v_collapsed_3009_);
v_clsEnabled_boxed_3020_ = lean_unbox(v_clsEnabled_3012_);
v_res_3021_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3008_, v_collapsed_boxed_3019_, v_tag_3010_, v_opts_3011_, v_clsEnabled_boxed_3020_, v_oldTraces_3013_, v_msg_3014_, v_resStartStop_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec_ref(v_opts_3011_);
return v_res_3021_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3025_; double v___x_3026_; 
v___x_3025_ = lean_unsigned_to_nat(1000000000u);
v___x_3026_ = lean_float_of_nat(v___x_3025_);
return v___x_3026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
lean_ctor_set(v___x_3031_, 2, v___x_3030_);
lean_ctor_set(v___x_3031_, 3, v___x_3030_);
lean_ctor_set(v___x_3031_, 4, v___x_3029_);
lean_ctor_set(v___x_3031_, 5, v___x_3029_);
lean_ctor_set(v___x_3031_, 6, v___x_3029_);
lean_ctor_set(v___x_3031_, 7, v___x_3029_);
lean_ctor_set(v___x_3031_, 8, v___x_3029_);
lean_ctor_set(v___x_3031_, 9, v___x_3029_);
return v___x_3031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3033_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
lean_ctor_set(v___x_3033_, 3, v___x_3032_);
lean_ctor_set(v___x_3033_, 4, v___x_3032_);
lean_ctor_set(v___x_3033_, 5, v___x_3032_);
return v___x_3033_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
lean_ctor_set(v___x_3035_, 3, v___x_3034_);
lean_ctor_set(v___x_3035_, 4, v___x_3034_);
return v___x_3035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3036_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3037_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3038_ = lean_box(1);
v___x_3039_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3040_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v___x_3039_);
lean_ctor_set(v___x_3041_, 2, v___x_3038_);
lean_ctor_set(v___x_3041_, 3, v___x_3037_);
lean_ctor_set(v___x_3041_, 4, v___x_3036_);
return v___x_3041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3044_ = l_Lean_Name_append(v___x_3043_, v___x_3042_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v___y_3050_; uint8_t v___y_3051_; lean_object* v_a_3052_; uint8_t v___y_3065_; uint8_t v___y_3066_; lean_object* v_a_3067_; lean_object* v_options_3083_; lean_object* v_inheritedTraceOptions_3084_; uint8_t v_hasTrace_3085_; uint8_t v___x_3086_; lean_object* v_a_3088_; 
v_options_3083_ = lean_ctor_get(v___y_3046_, 2);
v_inheritedTraceOptions_3084_ = lean_ctor_get(v___y_3046_, 13);
v_hasTrace_3085_ = lean_ctor_get_uint8(v_options_3083_, sizeof(void*)*1);
v___x_3086_ = lean_bool_not(v_hasTrace_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___f_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___y_3106_; lean_object* v___y_3107_; uint8_t v___y_3108_; lean_object* v_a_3109_; lean_object* v___y_3122_; lean_object* v___y_3123_; uint8_t v___y_3124_; uint8_t v_a_3125_; uint8_t v___y_3129_; uint8_t v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; uint8_t v___y_3133_; lean_object* v_a_3134_; uint8_t v___y_3136_; uint8_t v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; uint8_t v___y_3140_; lean_object* v_a_3141_; lean_object* v___y_3143_; lean_object* v___y_3144_; uint8_t v___y_3145_; lean_object* v_a_3146_; lean_object* v___y_3149_; lean_object* v___y_3150_; uint8_t v___y_3151_; lean_object* v_a_3152_; lean_object* v___y_3162_; lean_object* v___y_3163_; uint8_t v___y_3164_; uint8_t v_a_3165_; lean_object* v___y_3169_; uint8_t v___y_3170_; lean_object* v___y_3171_; uint8_t v___y_3172_; lean_object* v_a_3173_; lean_object* v___y_3175_; uint8_t v___y_3176_; lean_object* v___y_3177_; uint8_t v___y_3178_; lean_object* v_a_3179_; lean_object* v___y_3181_; lean_object* v___y_3182_; uint8_t v___y_3183_; lean_object* v_a_3184_; uint8_t v___y_3187_; uint8_t v_a_3297_; 
lean_inc(v_name_3045_);
v___f_3101_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3101_, 0, v_name_3045_);
v___x_3102_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3103_ = 1;
v___x_3104_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
if (v_hasTrace_3085_ == 0)
{
v_a_3297_ = v_hasTrace_3085_;
goto v___jp_3296_;
}
else
{
lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3379_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3084_, v_options_3083_, v___x_3379_);
if (v___x_3380_ == 0)
{
v_a_3297_ = v___x_3380_;
goto v___jp_3296_;
}
else
{
v___y_3187_ = v___x_3380_;
goto v___jp_3186_;
}
}
v___jp_3105_:
{
lean_object* v___x_3110_; double v___x_3111_; double v___x_3112_; double v___x_3113_; double v___x_3114_; double v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3110_ = lean_io_mono_nanos_now();
v___x_3111_ = lean_float_of_nat(v___y_3107_);
v___x_3112_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3113_ = lean_float_div(v___x_3111_, v___x_3112_);
v___x_3114_ = lean_float_of_nat(v___x_3110_);
v___x_3115_ = lean_float_div(v___x_3114_, v___x_3112_);
v___x_3116_ = lean_box_float(v___x_3113_);
v___x_3117_ = lean_box_float(v___x_3115_);
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3116_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_a_3109_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3102_, v___x_3103_, v___x_3104_, v_options_3083_, v___y_3108_, v___y_3106_, v___f_3101_, v___x_3119_, v___y_3046_, v___y_3047_);
return v___x_3120_;
}
v___jp_3121_:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = lean_box(v_a_3125_);
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
v___y_3106_ = v___y_3122_;
v___y_3107_ = v___y_3123_;
v___y_3108_ = v___y_3124_;
v_a_3109_ = v___x_3127_;
goto v___jp_3105_;
}
v___jp_3128_:
{
if (lean_obj_tag(v_a_3134_) == 0)
{
v___y_3122_ = v___y_3131_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___y_3133_;
v_a_3125_ = v___y_3130_;
goto v___jp_3121_;
}
else
{
lean_dec_ref_known(v_a_3134_, 1);
v___y_3122_ = v___y_3131_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___y_3133_;
v_a_3125_ = v___y_3129_;
goto v___jp_3121_;
}
}
v___jp_3135_:
{
if (lean_obj_tag(v_a_3141_) == 0)
{
v___y_3122_ = v___y_3138_;
v___y_3123_ = v___y_3139_;
v___y_3124_ = v___y_3140_;
v_a_3125_ = v___y_3137_;
goto v___jp_3121_;
}
else
{
lean_dec_ref_known(v_a_3141_, 1);
v___y_3122_ = v___y_3138_;
v___y_3123_ = v___y_3139_;
v___y_3124_ = v___y_3140_;
v_a_3125_ = v___y_3136_;
goto v___jp_3121_;
}
}
v___jp_3142_:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_a_3146_);
v___y_3106_ = v___y_3143_;
v___y_3107_ = v___y_3144_;
v___y_3108_ = v___y_3145_;
v_a_3109_ = v___x_3147_;
goto v___jp_3105_;
}
v___jp_3148_:
{
lean_object* v___x_3153_; double v___x_3154_; double v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3153_ = lean_io_get_num_heartbeats();
v___x_3154_ = lean_float_of_nat(v___y_3149_);
v___x_3155_ = lean_float_of_nat(v___x_3153_);
v___x_3156_ = lean_box_float(v___x_3154_);
v___x_3157_ = lean_box_float(v___x_3155_);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_a_3152_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3102_, v___x_3103_, v___x_3104_, v_options_3083_, v___y_3151_, v___y_3150_, v___f_3101_, v___x_3159_, v___y_3046_, v___y_3047_);
return v___x_3160_;
}
v___jp_3161_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_box(v_a_3165_);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
v___y_3149_ = v___y_3162_;
v___y_3150_ = v___y_3163_;
v___y_3151_ = v___y_3164_;
v_a_3152_ = v___x_3167_;
goto v___jp_3148_;
}
v___jp_3168_:
{
if (lean_obj_tag(v_a_3173_) == 0)
{
v___y_3162_ = v___y_3169_;
v___y_3163_ = v___y_3171_;
v___y_3164_ = v___y_3172_;
v_a_3165_ = v___x_3086_;
goto v___jp_3161_;
}
else
{
lean_dec_ref_known(v_a_3173_, 1);
v___y_3162_ = v___y_3169_;
v___y_3163_ = v___y_3171_;
v___y_3164_ = v___y_3172_;
v_a_3165_ = v___y_3170_;
goto v___jp_3161_;
}
}
v___jp_3174_:
{
if (lean_obj_tag(v_a_3179_) == 0)
{
v___y_3162_ = v___y_3175_;
v___y_3163_ = v___y_3177_;
v___y_3164_ = v___y_3178_;
v_a_3165_ = v___x_3086_;
goto v___jp_3161_;
}
else
{
lean_dec_ref_known(v_a_3179_, 1);
v___y_3162_ = v___y_3175_;
v___y_3163_ = v___y_3177_;
v___y_3164_ = v___y_3178_;
v_a_3165_ = v___y_3176_;
goto v___jp_3161_;
}
}
v___jp_3180_:
{
lean_object* v___x_3185_; 
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v_a_3184_);
v___y_3149_ = v___y_3181_;
v___y_3150_ = v___y_3182_;
v___y_3151_ = v___y_3183_;
v_a_3152_ = v___x_3185_;
goto v___jp_3148_;
}
v___jp_3186_:
{
lean_object* v___x_3188_; lean_object* v_a_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3188_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3047_);
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref(v___x_3188_);
v___x_3190_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3191_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3083_, v___x_3190_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v_env_3194_; lean_object* v___x_3195_; 
v___x_3192_ = lean_io_mono_nanos_now();
v___x_3193_ = lean_st_ref_get(v___y_3047_);
v_env_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc_ref(v_env_3194_);
lean_dec(v___x_3193_);
lean_inc(v_name_3045_);
v___x_3195_ = l_Lean_Meta_declFromEqLikeName(v_env_3194_, v_name_3045_);
if (lean_obj_tag(v___x_3195_) == 1)
{
lean_object* v_val_3196_; lean_object* v_fst_3197_; lean_object* v_snd_3198_; lean_object* v___x_3199_; lean_object* v_env_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_val_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_val_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v_fst_3197_ = lean_ctor_get(v_val_3196_, 0);
lean_inc_n(v_fst_3197_, 2);
v_snd_3198_ = lean_ctor_get(v_val_3196_, 1);
lean_inc_n(v_snd_3198_, 2);
lean_dec(v_val_3196_);
v___x_3199_ = lean_st_ref_get(v___y_3047_);
v_env_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc_ref(v_env_3200_);
lean_dec(v___x_3199_);
v___x_3201_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3200_, v_fst_3197_, v_snd_3198_);
v___x_3202_ = lean_name_eq(v_name_3045_, v___x_3201_);
lean_dec(v___x_3201_);
lean_dec(v_name_3045_);
if (v___x_3202_ == 0)
{
lean_dec(v_snd_3198_);
lean_dec(v_fst_3197_);
v___y_3122_ = v_a_3189_;
v___y_3123_ = v___x_3192_;
v___y_3124_ = v___y_3187_;
v_a_3125_ = v___x_3191_;
goto v___jp_3121_;
}
else
{
uint8_t v___x_3203_; 
lean_inc(v_snd_3198_);
v___x_3203_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3198_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; uint8_t v___x_3205_; 
v___x_3204_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3205_ = lean_string_dec_eq(v_snd_3198_, v___x_3204_);
lean_dec(v_snd_3198_);
if (v___x_3205_ == 0)
{
lean_dec(v_fst_3197_);
v___y_3122_ = v_a_3189_;
v___y_3123_ = v___x_3192_;
v___y_3124_ = v___y_3187_;
v_a_3125_ = v___x_3191_;
goto v___jp_3121_;
}
else
{
uint8_t v___x_3206_; uint8_t v___x_3207_; uint8_t v___x_3208_; lean_object* v___x_3209_; uint64_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3206_ = 1;
v___x_3207_ = 0;
v___x_3208_ = 2;
v___x_3209_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3209_, 0, v___x_3191_);
lean_ctor_set_uint8(v___x_3209_, 1, v___x_3191_);
lean_ctor_set_uint8(v___x_3209_, 2, v___x_3191_);
lean_ctor_set_uint8(v___x_3209_, 3, v___x_3191_);
lean_ctor_set_uint8(v___x_3209_, 4, v___x_3191_);
lean_ctor_set_uint8(v___x_3209_, 5, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 6, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 7, v___x_3191_);
lean_ctor_set_uint8(v___x_3209_, 8, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 9, v___x_3206_);
lean_ctor_set_uint8(v___x_3209_, 10, v___x_3207_);
lean_ctor_set_uint8(v___x_3209_, 11, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 12, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 13, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 14, v___x_3208_);
lean_ctor_set_uint8(v___x_3209_, 15, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 16, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 17, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, 18, v___x_3205_);
v___x_3210_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3209_);
v___x_3211_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set_uint64(v___x_3211_, sizeof(void*)*1, v___x_3210_);
v___x_3212_ = lean_box(1);
v___x_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3215_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3216_ = lean_box(0);
v___x_3217_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3217_, 0, v___x_3211_);
lean_ctor_set(v___x_3217_, 1, v___x_3212_);
lean_ctor_set(v___x_3217_, 2, v___x_3214_);
lean_ctor_set(v___x_3217_, 3, v___x_3215_);
lean_ctor_set(v___x_3217_, 4, v___x_3216_);
lean_ctor_set(v___x_3217_, 5, v___x_3213_);
lean_ctor_set(v___x_3217_, 6, v___x_3216_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7, v___x_3191_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 1, v___x_3191_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 2, v___x_3191_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 3, v___x_3202_);
v___x_3218_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3219_ = lean_st_mk_ref(v___x_3218_);
v___x_3220_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3197_, v___x_3202_, v___x_3217_, v___x_3219_, v___y_3046_, v___y_3047_);
lean_dec_ref_known(v___x_3217_, 7);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3222_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3222_ = lean_st_ref_get(v___x_3219_);
lean_dec(v___x_3219_);
lean_dec(v___x_3222_);
v___y_3136_ = v___x_3205_;
v___y_3137_ = v___x_3191_;
v___y_3138_ = v_a_3189_;
v___y_3139_ = v___x_3192_;
v___y_3140_ = v___y_3187_;
v_a_3141_ = v_a_3221_;
goto v___jp_3135_;
}
else
{
lean_dec(v___x_3219_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3223_; 
v_a_3223_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3220_, 1);
v___y_3136_ = v___x_3205_;
v___y_3137_ = v___x_3191_;
v___y_3138_ = v_a_3189_;
v___y_3139_ = v___x_3192_;
v___y_3140_ = v___y_3187_;
v_a_3141_ = v_a_3223_;
goto v___jp_3135_;
}
else
{
lean_object* v_a_3224_; 
v_a_3224_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3220_, 1);
v___y_3143_ = v_a_3189_;
v___y_3144_ = v___x_3192_;
v___y_3145_ = v___y_3187_;
v_a_3146_ = v_a_3224_;
goto v___jp_3142_;
}
}
}
}
else
{
uint8_t v___x_3225_; uint8_t v___x_3226_; uint8_t v___x_3227_; lean_object* v___x_3228_; uint64_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
lean_dec(v_snd_3198_);
v___x_3225_ = 1;
v___x_3226_ = 0;
v___x_3227_ = 2;
v___x_3228_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3228_, 0, v___x_3191_);
lean_ctor_set_uint8(v___x_3228_, 1, v___x_3191_);
lean_ctor_set_uint8(v___x_3228_, 2, v___x_3191_);
lean_ctor_set_uint8(v___x_3228_, 3, v___x_3191_);
lean_ctor_set_uint8(v___x_3228_, 4, v___x_3191_);
lean_ctor_set_uint8(v___x_3228_, 5, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 6, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 7, v___x_3191_);
lean_ctor_set_uint8(v___x_3228_, 8, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 9, v___x_3225_);
lean_ctor_set_uint8(v___x_3228_, 10, v___x_3226_);
lean_ctor_set_uint8(v___x_3228_, 11, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 12, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 13, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 14, v___x_3227_);
lean_ctor_set_uint8(v___x_3228_, 15, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 16, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 17, v___x_3203_);
lean_ctor_set_uint8(v___x_3228_, 18, v___x_3203_);
v___x_3229_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3228_);
v___x_3230_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
lean_ctor_set_uint64(v___x_3230_, sizeof(void*)*1, v___x_3229_);
v___x_3231_ = lean_box(1);
v___x_3232_ = lean_unsigned_to_nat(0u);
v___x_3233_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3234_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3236_, 0, v___x_3230_);
lean_ctor_set(v___x_3236_, 1, v___x_3231_);
lean_ctor_set(v___x_3236_, 2, v___x_3233_);
lean_ctor_set(v___x_3236_, 3, v___x_3234_);
lean_ctor_set(v___x_3236_, 4, v___x_3235_);
lean_ctor_set(v___x_3236_, 5, v___x_3232_);
lean_ctor_set(v___x_3236_, 6, v___x_3235_);
lean_ctor_set_uint8(v___x_3236_, sizeof(void*)*7, v___x_3191_);
lean_ctor_set_uint8(v___x_3236_, sizeof(void*)*7 + 1, v___x_3191_);
lean_ctor_set_uint8(v___x_3236_, sizeof(void*)*7 + 2, v___x_3191_);
lean_ctor_set_uint8(v___x_3236_, sizeof(void*)*7 + 3, v___x_3202_);
v___x_3237_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3238_ = lean_st_mk_ref(v___x_3237_);
v___x_3239_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3197_, v___x_3236_, v___x_3238_, v___y_3046_, v___y_3047_);
lean_dec_ref_known(v___x_3236_, 7);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
v___x_3241_ = lean_st_ref_get(v___x_3238_);
lean_dec(v___x_3238_);
lean_dec(v___x_3241_);
v___y_3129_ = v___x_3203_;
v___y_3130_ = v___x_3191_;
v___y_3131_ = v_a_3189_;
v___y_3132_ = v___x_3192_;
v___y_3133_ = v___y_3187_;
v_a_3134_ = v_a_3240_;
goto v___jp_3128_;
}
else
{
lean_dec(v___x_3238_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3242_; 
v_a_3242_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3239_, 1);
v___y_3129_ = v___x_3203_;
v___y_3130_ = v___x_3191_;
v___y_3131_ = v_a_3189_;
v___y_3132_ = v___x_3192_;
v___y_3133_ = v___y_3187_;
v_a_3134_ = v_a_3242_;
goto v___jp_3128_;
}
else
{
lean_object* v_a_3243_; 
v_a_3243_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3239_, 1);
v___y_3143_ = v_a_3189_;
v___y_3144_ = v___x_3192_;
v___y_3145_ = v___y_3187_;
v_a_3146_ = v_a_3243_;
goto v___jp_3142_;
}
}
}
}
}
else
{
lean_dec(v___x_3195_);
lean_dec(v_name_3045_);
v___y_3122_ = v_a_3189_;
v___y_3123_ = v___x_3192_;
v___y_3124_ = v___y_3187_;
v_a_3125_ = v___x_3191_;
goto v___jp_3121_;
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v_env_3246_; lean_object* v___x_3247_; 
v___x_3244_ = lean_io_get_num_heartbeats();
v___x_3245_ = lean_st_ref_get(v___y_3047_);
v_env_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc_ref(v_env_3246_);
lean_dec(v___x_3245_);
lean_inc(v_name_3045_);
v___x_3247_ = l_Lean_Meta_declFromEqLikeName(v_env_3246_, v_name_3045_);
if (lean_obj_tag(v___x_3247_) == 1)
{
lean_object* v_val_3248_; lean_object* v_fst_3249_; lean_object* v_snd_3250_; lean_object* v___x_3251_; lean_object* v_env_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v_val_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_val_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v_fst_3249_ = lean_ctor_get(v_val_3248_, 0);
lean_inc_n(v_fst_3249_, 2);
v_snd_3250_ = lean_ctor_get(v_val_3248_, 1);
lean_inc_n(v_snd_3250_, 2);
lean_dec(v_val_3248_);
v___x_3251_ = lean_st_ref_get(v___y_3047_);
v_env_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc_ref(v_env_3252_);
lean_dec(v___x_3251_);
v___x_3253_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3252_, v_fst_3249_, v_snd_3250_);
v___x_3254_ = lean_name_eq(v_name_3045_, v___x_3253_);
lean_dec(v___x_3253_);
lean_dec(v_name_3045_);
if (v___x_3254_ == 0)
{
lean_dec(v_snd_3250_);
lean_dec(v_fst_3249_);
v___y_3162_ = v___x_3244_;
v___y_3163_ = v_a_3189_;
v___y_3164_ = v___y_3187_;
v_a_3165_ = v___x_3086_;
goto v___jp_3161_;
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
v___y_3162_ = v___x_3244_;
v___y_3163_ = v_a_3189_;
v___y_3164_ = v___y_3187_;
v_a_3165_ = v___x_3086_;
goto v___jp_3161_;
}
else
{
uint8_t v___x_3258_; uint8_t v___x_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; uint64_t v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3258_ = 1;
v___x_3259_ = 0;
v___x_3260_ = 2;
v___x_3261_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3261_, 0, v___x_3086_);
lean_ctor_set_uint8(v___x_3261_, 1, v___x_3086_);
lean_ctor_set_uint8(v___x_3261_, 2, v___x_3086_);
lean_ctor_set_uint8(v___x_3261_, 3, v___x_3086_);
lean_ctor_set_uint8(v___x_3261_, 4, v___x_3086_);
lean_ctor_set_uint8(v___x_3261_, 5, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 6, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 7, v___x_3086_);
lean_ctor_set_uint8(v___x_3261_, 8, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 9, v___x_3258_);
lean_ctor_set_uint8(v___x_3261_, 10, v___x_3259_);
lean_ctor_set_uint8(v___x_3261_, 11, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 12, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 13, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 14, v___x_3260_);
lean_ctor_set_uint8(v___x_3261_, 15, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 16, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 17, v___x_3191_);
lean_ctor_set_uint8(v___x_3261_, 18, v___x_3191_);
v___x_3262_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3261_);
v___x_3263_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3263_, 0, v___x_3261_);
lean_ctor_set_uint64(v___x_3263_, sizeof(void*)*1, v___x_3262_);
v___x_3264_ = lean_box(1);
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3267_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3269_, 0, v___x_3263_);
lean_ctor_set(v___x_3269_, 1, v___x_3264_);
lean_ctor_set(v___x_3269_, 2, v___x_3266_);
lean_ctor_set(v___x_3269_, 3, v___x_3267_);
lean_ctor_set(v___x_3269_, 4, v___x_3268_);
lean_ctor_set(v___x_3269_, 5, v___x_3265_);
lean_ctor_set(v___x_3269_, 6, v___x_3268_);
lean_ctor_set_uint8(v___x_3269_, sizeof(void*)*7, v___x_3086_);
lean_ctor_set_uint8(v___x_3269_, sizeof(void*)*7 + 1, v___x_3086_);
lean_ctor_set_uint8(v___x_3269_, sizeof(void*)*7 + 2, v___x_3086_);
lean_ctor_set_uint8(v___x_3269_, sizeof(void*)*7 + 3, v___x_3191_);
v___x_3270_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3271_ = lean_st_mk_ref(v___x_3270_);
v___x_3272_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3249_, v___x_3191_, v___x_3269_, v___x_3271_, v___y_3046_, v___y_3047_);
lean_dec_ref_known(v___x_3269_, 7);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3274_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref_known(v___x_3272_, 1);
v___x_3274_ = lean_st_ref_get(v___x_3271_);
lean_dec(v___x_3271_);
lean_dec(v___x_3274_);
v___y_3175_ = v___x_3244_;
v___y_3176_ = v___x_3191_;
v___y_3177_ = v_a_3189_;
v___y_3178_ = v___y_3187_;
v_a_3179_ = v_a_3273_;
goto v___jp_3174_;
}
else
{
lean_dec(v___x_3271_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3275_; 
v_a_3275_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3272_, 1);
v___y_3175_ = v___x_3244_;
v___y_3176_ = v___x_3191_;
v___y_3177_ = v_a_3189_;
v___y_3178_ = v___y_3187_;
v_a_3179_ = v_a_3275_;
goto v___jp_3174_;
}
else
{
lean_object* v_a_3276_; 
v_a_3276_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3272_, 1);
v___y_3181_ = v___x_3244_;
v___y_3182_ = v_a_3189_;
v___y_3183_ = v___y_3187_;
v_a_3184_ = v_a_3276_;
goto v___jp_3180_;
}
}
}
}
else
{
uint8_t v___x_3277_; uint8_t v___x_3278_; uint8_t v___x_3279_; lean_object* v___x_3280_; uint64_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_dec(v_snd_3250_);
v___x_3277_ = 1;
v___x_3278_ = 0;
v___x_3279_ = 2;
v___x_3280_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3280_, 0, v___x_3086_);
lean_ctor_set_uint8(v___x_3280_, 1, v___x_3086_);
lean_ctor_set_uint8(v___x_3280_, 2, v___x_3086_);
lean_ctor_set_uint8(v___x_3280_, 3, v___x_3086_);
lean_ctor_set_uint8(v___x_3280_, 4, v___x_3086_);
lean_ctor_set_uint8(v___x_3280_, 5, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 6, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 7, v___x_3086_);
lean_ctor_set_uint8(v___x_3280_, 8, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 9, v___x_3277_);
lean_ctor_set_uint8(v___x_3280_, 10, v___x_3278_);
lean_ctor_set_uint8(v___x_3280_, 11, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 12, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 13, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 14, v___x_3279_);
lean_ctor_set_uint8(v___x_3280_, 15, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 16, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 17, v___x_3191_);
lean_ctor_set_uint8(v___x_3280_, 18, v___x_3191_);
v___x_3281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3280_);
v___x_3282_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set_uint64(v___x_3282_, sizeof(void*)*1, v___x_3281_);
v___x_3283_ = lean_box(1);
v___x_3284_ = lean_unsigned_to_nat(0u);
v___x_3285_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3286_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3288_, 0, v___x_3282_);
lean_ctor_set(v___x_3288_, 1, v___x_3283_);
lean_ctor_set(v___x_3288_, 2, v___x_3285_);
lean_ctor_set(v___x_3288_, 3, v___x_3286_);
lean_ctor_set(v___x_3288_, 4, v___x_3287_);
lean_ctor_set(v___x_3288_, 5, v___x_3284_);
lean_ctor_set(v___x_3288_, 6, v___x_3287_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*7, v___x_3086_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*7 + 1, v___x_3086_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*7 + 2, v___x_3086_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*7 + 3, v___x_3191_);
v___x_3289_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3290_ = lean_st_mk_ref(v___x_3289_);
v___x_3291_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3249_, v___x_3288_, v___x_3290_, v___y_3046_, v___y_3047_);
lean_dec_ref_known(v___x_3288_, 7);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3293_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3293_ = lean_st_ref_get(v___x_3290_);
lean_dec(v___x_3290_);
lean_dec(v___x_3293_);
v___y_3169_ = v___x_3244_;
v___y_3170_ = v___x_3191_;
v___y_3171_ = v_a_3189_;
v___y_3172_ = v___y_3187_;
v_a_3173_ = v_a_3292_;
goto v___jp_3168_;
}
else
{
lean_dec(v___x_3290_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3294_; 
v_a_3294_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3291_, 1);
v___y_3169_ = v___x_3244_;
v___y_3170_ = v___x_3191_;
v___y_3171_ = v_a_3189_;
v___y_3172_ = v___y_3187_;
v_a_3173_ = v_a_3294_;
goto v___jp_3168_;
}
else
{
lean_object* v_a_3295_; 
v_a_3295_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3291_, 1);
v___y_3181_ = v___x_3244_;
v___y_3182_ = v_a_3189_;
v___y_3183_ = v___y_3187_;
v_a_3184_ = v_a_3295_;
goto v___jp_3180_;
}
}
}
}
}
else
{
lean_dec(v___x_3247_);
lean_dec(v_name_3045_);
v___y_3162_ = v___x_3244_;
v___y_3163_ = v_a_3189_;
v___y_3164_ = v___y_3187_;
v_a_3165_ = v___x_3086_;
goto v___jp_3161_;
}
}
}
v___jp_3296_:
{
lean_object* v___x_3298_; uint8_t v___x_3299_; 
v___x_3298_ = l_Lean_trace_profiler;
v___x_3299_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3083_, v___x_3298_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v_env_3301_; lean_object* v___x_3302_; 
lean_dec_ref(v___f_3101_);
v___x_3300_ = lean_st_ref_get(v___y_3047_);
v_env_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_ref(v_env_3301_);
lean_dec(v___x_3300_);
lean_inc(v_name_3045_);
v___x_3302_ = l_Lean_Meta_declFromEqLikeName(v_env_3301_, v_name_3045_);
if (lean_obj_tag(v___x_3302_) == 1)
{
lean_object* v_val_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3376_; 
v_val_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3376_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_val_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3376_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_fst_3307_; lean_object* v_snd_3308_; lean_object* v___x_3309_; lean_object* v_env_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v_fst_3307_ = lean_ctor_get(v_val_3303_, 0);
lean_inc_n(v_fst_3307_, 2);
v_snd_3308_ = lean_ctor_get(v_val_3303_, 1);
lean_inc_n(v_snd_3308_, 2);
lean_dec(v_val_3303_);
v___x_3309_ = lean_st_ref_get(v___y_3047_);
v_env_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc_ref(v_env_3310_);
lean_dec(v___x_3309_);
v___x_3311_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3310_, v_fst_3307_, v_snd_3308_);
v___x_3312_ = lean_name_eq(v_name_3045_, v___x_3311_);
lean_dec(v___x_3311_);
lean_dec(v_name_3045_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
lean_dec(v_snd_3308_);
lean_dec(v_fst_3307_);
v___x_3313_ = lean_box(v___x_3299_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3313_);
v___x_3315_ = v___x_3305_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
else
{
uint8_t v___x_3317_; 
lean_inc(v_snd_3308_);
v___x_3317_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3308_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3319_ = lean_string_dec_eq(v_snd_3308_, v___x_3318_);
lean_dec(v_snd_3308_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
lean_dec(v_fst_3307_);
v___x_3320_ = lean_box(v___x_3299_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3320_);
v___x_3322_ = v___x_3305_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
else
{
uint8_t v___x_3324_; uint8_t v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; uint64_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_del_object(v___x_3305_);
v___x_3324_ = 1;
v___x_3325_ = 0;
v___x_3326_ = 2;
v___x_3327_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3327_, 0, v___x_3299_);
lean_ctor_set_uint8(v___x_3327_, 1, v___x_3299_);
lean_ctor_set_uint8(v___x_3327_, 2, v___x_3299_);
lean_ctor_set_uint8(v___x_3327_, 3, v___x_3299_);
lean_ctor_set_uint8(v___x_3327_, 4, v___x_3299_);
lean_ctor_set_uint8(v___x_3327_, 5, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 6, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 7, v___x_3299_);
lean_ctor_set_uint8(v___x_3327_, 8, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 9, v___x_3324_);
lean_ctor_set_uint8(v___x_3327_, 10, v___x_3325_);
lean_ctor_set_uint8(v___x_3327_, 11, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 12, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 13, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 14, v___x_3326_);
lean_ctor_set_uint8(v___x_3327_, 15, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 16, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 17, v___x_3319_);
lean_ctor_set_uint8(v___x_3327_, 18, v___x_3319_);
v___x_3328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3327_);
v___x_3329_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set_uint64(v___x_3329_, sizeof(void*)*1, v___x_3328_);
v___x_3330_ = lean_box(1);
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3335_, 0, v___x_3329_);
lean_ctor_set(v___x_3335_, 1, v___x_3330_);
lean_ctor_set(v___x_3335_, 2, v___x_3332_);
lean_ctor_set(v___x_3335_, 3, v___x_3333_);
lean_ctor_set(v___x_3335_, 4, v___x_3334_);
lean_ctor_set(v___x_3335_, 5, v___x_3331_);
lean_ctor_set(v___x_3335_, 6, v___x_3334_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7, v___x_3299_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7 + 1, v___x_3299_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7 + 2, v___x_3299_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7 + 3, v___x_3312_);
v___x_3336_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3337_ = lean_st_mk_ref(v___x_3336_);
v___x_3338_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3307_, v___x_3312_, v___x_3335_, v___x_3337_, v___y_3046_, v___y_3047_);
lean_dec_ref_known(v___x_3335_, 7);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3340_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = lean_st_ref_get(v___x_3337_);
lean_dec(v___x_3337_);
lean_dec(v___x_3340_);
v___y_3050_ = v___x_3299_;
v___y_3051_ = v___x_3319_;
v_a_3052_ = v_a_3339_;
goto v___jp_3049_;
}
else
{
lean_dec(v___x_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3341_; 
v_a_3341_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3338_, 1);
v___y_3050_ = v___x_3299_;
v___y_3051_ = v___x_3319_;
v_a_3052_ = v_a_3341_;
goto v___jp_3049_;
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
v_a_3342_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3338_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3338_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
}
else
{
uint8_t v___x_3350_; uint8_t v___x_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; uint64_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec(v_snd_3308_);
lean_del_object(v___x_3305_);
v___x_3350_ = 1;
v___x_3351_ = 0;
v___x_3352_ = 2;
v___x_3353_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3353_, 0, v___x_3299_);
lean_ctor_set_uint8(v___x_3353_, 1, v___x_3299_);
lean_ctor_set_uint8(v___x_3353_, 2, v___x_3299_);
lean_ctor_set_uint8(v___x_3353_, 3, v___x_3299_);
lean_ctor_set_uint8(v___x_3353_, 4, v___x_3299_);
lean_ctor_set_uint8(v___x_3353_, 5, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 6, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 7, v___x_3299_);
lean_ctor_set_uint8(v___x_3353_, 8, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 9, v___x_3350_);
lean_ctor_set_uint8(v___x_3353_, 10, v___x_3351_);
lean_ctor_set_uint8(v___x_3353_, 11, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 12, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 13, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 14, v___x_3352_);
lean_ctor_set_uint8(v___x_3353_, 15, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 16, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 17, v___x_3317_);
lean_ctor_set_uint8(v___x_3353_, 18, v___x_3317_);
v___x_3354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3353_);
v___x_3355_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set_uint64(v___x_3355_, sizeof(void*)*1, v___x_3354_);
v___x_3356_ = lean_box(1);
v___x_3357_ = lean_unsigned_to_nat(0u);
v___x_3358_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3359_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3360_ = lean_box(0);
v___x_3361_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3361_, 0, v___x_3355_);
lean_ctor_set(v___x_3361_, 1, v___x_3356_);
lean_ctor_set(v___x_3361_, 2, v___x_3358_);
lean_ctor_set(v___x_3361_, 3, v___x_3359_);
lean_ctor_set(v___x_3361_, 4, v___x_3360_);
lean_ctor_set(v___x_3361_, 5, v___x_3357_);
lean_ctor_set(v___x_3361_, 6, v___x_3360_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*7, v___x_3299_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*7 + 1, v___x_3299_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*7 + 2, v___x_3299_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*7 + 3, v___x_3312_);
v___x_3362_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3363_ = lean_st_mk_ref(v___x_3362_);
v___x_3364_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3307_, v___x_3361_, v___x_3363_, v___y_3046_, v___y_3047_);
lean_dec_ref_known(v___x_3361_, 7);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___x_3366_ = lean_st_ref_get(v___x_3363_);
lean_dec(v___x_3363_);
lean_dec(v___x_3366_);
v___y_3065_ = v___x_3299_;
v___y_3066_ = v___x_3317_;
v_a_3067_ = v_a_3365_;
goto v___jp_3064_;
}
else
{
lean_dec(v___x_3363_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3367_; 
v_a_3367_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3364_, 1);
v___y_3065_ = v___x_3299_;
v___y_3066_ = v___x_3317_;
v_a_3067_ = v_a_3367_;
goto v___jp_3064_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
v_a_3368_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3364_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3364_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
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
lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec(v___x_3302_);
lean_dec(v_name_3045_);
v___x_3377_ = lean_box(v___x_3299_);
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
}
else
{
v___y_3187_ = v_a_3297_;
goto v___jp_3186_;
}
}
}
else
{
lean_object* v___x_3381_; lean_object* v_env_3382_; lean_object* v___x_3383_; 
v___x_3381_ = lean_st_ref_get(v___y_3047_);
v_env_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc_ref(v_env_3382_);
lean_dec(v___x_3381_);
lean_inc(v_name_3045_);
v___x_3383_ = l_Lean_Meta_declFromEqLikeName(v_env_3382_, v_name_3045_);
if (lean_obj_tag(v___x_3383_) == 1)
{
lean_object* v_val_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3465_; 
v_val_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3465_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_val_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3465_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v_fst_3388_; lean_object* v_snd_3389_; lean_object* v___x_3390_; lean_object* v_env_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v_fst_3388_ = lean_ctor_get(v_val_3384_, 0);
lean_inc_n(v_fst_3388_, 2);
v_snd_3389_ = lean_ctor_get(v_val_3384_, 1);
lean_inc_n(v_snd_3389_, 2);
lean_dec(v_val_3384_);
v___x_3390_ = lean_st_ref_get(v___y_3047_);
v_env_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc_ref(v_env_3391_);
lean_dec(v___x_3390_);
v___x_3392_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3391_, v_fst_3388_, v_snd_3389_);
v___x_3393_ = lean_name_eq(v_name_3045_, v___x_3392_);
lean_dec(v___x_3392_);
lean_dec(v_name_3045_);
if (v___x_3393_ == 0)
{
lean_dec(v_snd_3389_);
lean_dec(v_fst_3388_);
lean_del_object(v___x_3386_);
goto v___jp_3079_;
}
else
{
uint8_t v___x_3394_; lean_object* v_a_3396_; 
lean_inc(v_snd_3389_);
v___x_3394_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3389_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3411_ = lean_string_dec_eq(v_snd_3389_, v___x_3410_);
lean_dec(v_snd_3389_);
if (v___x_3411_ == 0)
{
lean_dec(v_fst_3388_);
lean_del_object(v___x_3386_);
goto v___jp_3079_;
}
else
{
uint8_t v___x_3412_; uint8_t v___x_3413_; uint8_t v___x_3414_; lean_object* v___x_3415_; uint64_t v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3412_ = 1;
v___x_3413_ = 0;
v___x_3414_ = 2;
v___x_3415_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3415_, 0, v___x_3394_);
lean_ctor_set_uint8(v___x_3415_, 1, v___x_3394_);
lean_ctor_set_uint8(v___x_3415_, 2, v___x_3394_);
lean_ctor_set_uint8(v___x_3415_, 3, v___x_3394_);
lean_ctor_set_uint8(v___x_3415_, 4, v___x_3394_);
lean_ctor_set_uint8(v___x_3415_, 5, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 6, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 7, v___x_3394_);
lean_ctor_set_uint8(v___x_3415_, 8, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 9, v___x_3412_);
lean_ctor_set_uint8(v___x_3415_, 10, v___x_3413_);
lean_ctor_set_uint8(v___x_3415_, 11, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 12, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 13, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 14, v___x_3414_);
lean_ctor_set_uint8(v___x_3415_, 15, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 16, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 17, v___x_3086_);
lean_ctor_set_uint8(v___x_3415_, 18, v___x_3086_);
v___x_3416_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3415_);
v___x_3417_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set_uint64(v___x_3417_, sizeof(void*)*1, v___x_3416_);
v___x_3418_ = lean_box(1);
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3421_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3422_ = lean_box(0);
v___x_3423_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3423_, 0, v___x_3417_);
lean_ctor_set(v___x_3423_, 1, v___x_3418_);
lean_ctor_set(v___x_3423_, 2, v___x_3420_);
lean_ctor_set(v___x_3423_, 3, v___x_3421_);
lean_ctor_set(v___x_3423_, 4, v___x_3422_);
lean_ctor_set(v___x_3423_, 5, v___x_3419_);
lean_ctor_set(v___x_3423_, 6, v___x_3422_);
lean_ctor_set_uint8(v___x_3423_, sizeof(void*)*7, v___x_3394_);
lean_ctor_set_uint8(v___x_3423_, sizeof(void*)*7 + 1, v___x_3394_);
lean_ctor_set_uint8(v___x_3423_, sizeof(void*)*7 + 2, v___x_3394_);
lean_ctor_set_uint8(v___x_3423_, sizeof(void*)*7 + 3, v___x_3086_);
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3425_ = lean_st_mk_ref(v___x_3424_);
v___x_3426_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3388_, v___x_3086_, v___x_3423_, v___x_3425_, v___y_3046_, v___y_3047_);
lean_dec_ref_known(v___x_3423_, 7);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v___x_3428_ = lean_st_ref_get(v___x_3425_);
lean_dec(v___x_3425_);
lean_dec(v___x_3428_);
v_a_3396_ = v_a_3427_;
goto v___jp_3395_;
}
else
{
lean_dec(v___x_3425_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3429_; 
v_a_3429_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3426_, 1);
v_a_3396_ = v_a_3429_;
goto v___jp_3395_;
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_del_object(v___x_3386_);
v_a_3430_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3426_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3426_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
else
{
uint8_t v___x_3438_; uint8_t v___x_3439_; uint8_t v___x_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; uint64_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec(v_snd_3389_);
lean_del_object(v___x_3386_);
v___x_3438_ = 0;
v___x_3439_ = 1;
v___x_3440_ = 0;
v___x_3441_ = 2;
v___x_3442_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3442_, 0, v___x_3438_);
lean_ctor_set_uint8(v___x_3442_, 1, v___x_3438_);
lean_ctor_set_uint8(v___x_3442_, 2, v___x_3438_);
lean_ctor_set_uint8(v___x_3442_, 3, v___x_3438_);
lean_ctor_set_uint8(v___x_3442_, 4, v___x_3438_);
lean_ctor_set_uint8(v___x_3442_, 5, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 6, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 7, v___x_3438_);
lean_ctor_set_uint8(v___x_3442_, 8, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 9, v___x_3439_);
lean_ctor_set_uint8(v___x_3442_, 10, v___x_3440_);
lean_ctor_set_uint8(v___x_3442_, 11, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 12, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 13, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 14, v___x_3441_);
lean_ctor_set_uint8(v___x_3442_, 15, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 16, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 17, v___x_3086_);
lean_ctor_set_uint8(v___x_3442_, 18, v___x_3086_);
v___x_3443_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set_uint64(v___x_3444_, sizeof(void*)*1, v___x_3443_);
v___x_3445_ = lean_box(1);
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3449_ = lean_box(0);
v___x_3450_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3450_, 0, v___x_3444_);
lean_ctor_set(v___x_3450_, 1, v___x_3445_);
lean_ctor_set(v___x_3450_, 2, v___x_3447_);
lean_ctor_set(v___x_3450_, 3, v___x_3448_);
lean_ctor_set(v___x_3450_, 4, v___x_3449_);
lean_ctor_set(v___x_3450_, 5, v___x_3446_);
lean_ctor_set(v___x_3450_, 6, v___x_3449_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*7, v___x_3438_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*7 + 1, v___x_3438_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*7 + 2, v___x_3438_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*7 + 3, v___x_3086_);
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3452_ = lean_st_mk_ref(v___x_3451_);
v___x_3453_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3388_, v___x_3450_, v___x_3452_, v___y_3046_, v___y_3047_);
lean_dec_ref_known(v___x_3450_, 7);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = lean_st_ref_get(v___x_3452_);
lean_dec(v___x_3452_);
lean_dec(v___x_3455_);
v_a_3088_ = v_a_3454_;
goto v___jp_3087_;
}
else
{
lean_dec(v___x_3452_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3456_; 
v_a_3456_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3453_, 1);
v_a_3088_ = v_a_3456_;
goto v___jp_3087_;
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
v_a_3457_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3453_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3453_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
v___jp_3395_:
{
if (lean_obj_tag(v_a_3396_) == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3397_ = lean_box(v___x_3394_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3397_);
v___x_3399_ = v___x_3386_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
else
{
lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3408_; 
lean_del_object(v___x_3386_);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_a_3396_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v_a_3396_, 0);
lean_dec(v_unused_3409_);
v___x_3402_ = v_a_3396_;
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
else
{
lean_dec(v_a_3396_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = lean_box(v___x_3086_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set_tag(v___x_3402_, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3404_);
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3383_);
lean_dec(v_name_3045_);
goto v___jp_3079_;
}
}
v___jp_3049_:
{
if (lean_obj_tag(v_a_3052_) == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_box(v___y_3050_);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
else
{
lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3062_; 
v_isSharedCheck_3062_ = !lean_is_exclusive(v_a_3052_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v_a_3052_, 0);
lean_dec(v_unused_3063_);
v___x_3056_ = v_a_3052_;
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
else
{
lean_dec(v_a_3052_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = lean_box(v___y_3051_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3058_);
v___x_3060_ = v___x_3056_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
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
v___jp_3064_:
{
if (lean_obj_tag(v_a_3067_) == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_box(v___y_3065_);
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
else
{
lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3077_; 
v_isSharedCheck_3077_ = !lean_is_exclusive(v_a_3067_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v_a_3067_, 0);
lean_dec(v_unused_3078_);
v___x_3071_ = v_a_3067_;
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
else
{
lean_dec(v_a_3067_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_box(v___y_3066_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3073_);
v___x_3075_ = v___x_3071_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
v___jp_3079_:
{
uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = 0;
v___x_3081_ = lean_box(v___x_3080_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
v___jp_3087_:
{
if (lean_obj_tag(v_a_3088_) == 0)
{
uint8_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = 0;
v___x_3090_ = lean_box(v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
else
{
lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3099_; 
v_isSharedCheck_3099_ = !lean_is_exclusive(v_a_3088_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v_a_3088_, 0);
lean_dec(v_unused_3100_);
v___x_3093_ = v_a_3088_;
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
else
{
lean_dec(v_a_3088_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = lean_box(v___x_3086_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set_tag(v___x_3093_, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3095_);
v___x_3097_ = v___x_3093_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
return v_res_3470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_unsigned_to_nat(3137104340u);
v___x_3513_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3514_ = l_Lean_Name_num___override(v___x_3513_, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3518_ = l_Lean_Name_str___override(v___x_3517_, v___x_3516_);
return v___x_3518_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3521_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3522_ = l_Lean_Name_str___override(v___x_3521_, v___x_3520_);
return v___x_3522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3523_ = lean_unsigned_to_nat(2u);
v___x_3524_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3525_ = l_Lean_Name_num___override(v___x_3524_, v___x_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3527_; lean_object* v___x_3528_; 
v___f_3527_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3528_ = l_Lean_registerReservedNameAction(v___f_3527_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3529_; uint8_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_dec_ref_known(v___x_3528_, 1);
v___x_3529_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3530_ = 0;
v___x_3531_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3532_ = l_Lean_registerTraceClass(v___x_3529_, v___x_3530_, v___x_3531_);
return v___x_3532_;
}
else
{
return v___x_3528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3535_, lean_object* v_x_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3536_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3541_, lean_object* v_x_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3541_, v_x_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
return v_res_3546_;
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
