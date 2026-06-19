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
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
uint8_t v___x_243_; 
lean_inc(v_head_229_);
lean_inc_ref(v_env_226_);
v___x_243_ = lean_is_matcher(v_env_226_, v_head_229_);
if (v___x_243_ == 0)
{
v___y_234_ = v___x_242_;
goto v___jp_233_;
}
else
{
v_as_x27_227_ = v_tail_230_;
v_b_228_ = v___x_232_;
goto _start;
}
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
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_524_; 
v_val_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_524_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_524_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_524_;
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
v___x_501_ = lean_is_matcher(v_env_500_, v_declName_479_);
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
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_519_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_519_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_519_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_519_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v___x_509_; 
v___x_509_ = lean_unbox(v_a_505_);
lean_dec(v_a_505_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = 1;
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
else
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_box(v___x_501_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_515_);
v___x_517_ = v___x_507_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
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
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec_ref(v_sig_498_);
v___x_520_ = lean_box(v___x_491_);
if (v_isShared_496_ == 0)
{
lean_ctor_set_tag(v___x_495_, 0);
lean_ctor_set(v___x_495_, 0, v___x_520_);
v___x_522_ = v___x_495_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
return v_res_531_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_537_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_540_);
return v_res_542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_543_; lean_object* v___f_544_; 
v___x_543_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_544_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_544_, 0, v___x_543_);
return v___f_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___f_546_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_547_ = lean_box(0);
v___x_548_ = lean_box(1);
v___x_549_ = l_Lean_registerEnvExtension___redArg(v___f_546_, v___x_547_, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_552_, lean_object* v_opt_553_){
_start:
{
lean_object* v_name_554_; lean_object* v_defValue_555_; lean_object* v_map_556_; lean_object* v___x_557_; 
v_name_554_ = lean_ctor_get(v_opt_553_, 0);
v_defValue_555_ = lean_ctor_get(v_opt_553_, 1);
v_map_556_ = lean_ctor_get(v_opts_552_, 0);
v___x_557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_556_, v_name_554_);
if (lean_obj_tag(v___x_557_) == 0)
{
uint8_t v___x_558_; 
v___x_558_ = lean_unbox(v_defValue_555_);
return v___x_558_;
}
else
{
lean_object* v_val_559_; 
v_val_559_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v___x_557_, 1);
if (lean_obj_tag(v_val_559_) == 1)
{
uint8_t v_v_560_; 
v_v_560_ = lean_ctor_get_uint8(v_val_559_, 0);
lean_dec_ref_known(v_val_559_, 0);
return v_v_560_;
}
else
{
uint8_t v___x_561_; 
lean_dec(v_val_559_);
v___x_561_ = lean_unbox(v_defValue_555_);
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_562_, lean_object* v_opt_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_562_, v_opt_563_);
lean_dec_ref(v_opt_563_);
lean_dec_ref(v_opts_562_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_opts_566_, lean_object* v_opt_567_){
_start:
{
lean_object* v_name_568_; lean_object* v_defValue_569_; lean_object* v_map_570_; lean_object* v___x_571_; 
v_name_568_ = lean_ctor_get(v_opt_567_, 0);
v_defValue_569_ = lean_ctor_get(v_opt_567_, 1);
v_map_570_ = lean_ctor_get(v_opts_566_, 0);
v___x_571_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_570_, v_name_568_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_inc(v_defValue_569_);
return v_defValue_569_;
}
else
{
lean_object* v_val_572_; 
v_val_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v___x_571_, 1);
if (lean_obj_tag(v_val_572_) == 3)
{
lean_object* v_v_573_; 
v_v_573_ = lean_ctor_get(v_val_572_, 0);
lean_inc(v_v_573_);
lean_dec_ref_known(v_val_572_, 1);
return v_v_573_;
}
else
{
lean_dec(v_val_572_);
lean_inc(v_defValue_569_);
return v_defValue_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_opts_574_, lean_object* v_opt_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_574_, v_opt_575_);
lean_dec_ref(v_opt_575_);
lean_dec_ref(v_opts_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_580_, size_t v_sz_581_, size_t v_i_582_, lean_object* v_b_583_){
_start:
{
lean_object* v_a_585_; uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_lt(v_i_582_, v_sz_581_);
if (v___x_589_ == 0)
{
return v_b_583_;
}
else
{
lean_object* v_a_590_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v_map_593_; uint8_t v_hasTrace_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_607_; 
v_a_590_ = lean_array_uget_borrowed(v_as_580_, v_i_582_);
v_fst_591_ = lean_ctor_get(v_a_590_, 0);
v_snd_592_ = lean_ctor_get(v_a_590_, 1);
v_map_593_ = lean_ctor_get(v_b_583_, 0);
v_hasTrace_594_ = lean_ctor_get_uint8(v_b_583_, sizeof(void*)*1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_b_583_);
if (v_isSharedCheck_607_ == 0)
{
v___x_596_ = v_b_583_;
v_isShared_597_ = v_isSharedCheck_607_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_map_593_);
lean_dec(v_b_583_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_607_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; 
lean_inc(v_snd_592_);
lean_inc(v_fst_591_);
v___x_598_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_591_, v_snd_592_, v_map_593_);
if (v_hasTrace_594_ == 0)
{
lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_602_; 
v___x_599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_600_ = l_Lean_Name_isPrefixOf(v___x_599_, v_fst_591_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_602_ = v___x_596_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_598_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*1, v___x_600_);
v_a_585_ = v___x_602_;
goto v___jp_584_;
}
}
else
{
lean_object* v___x_605_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_605_ = v___x_596_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_598_);
lean_ctor_set_uint8(v_reuseFailAlloc_606_, sizeof(void*)*1, v_hasTrace_594_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v_a_585_ = v___x_605_;
goto v___jp_584_;
}
}
}
}
v___jp_584_:
{
size_t v___x_586_; size_t v___x_587_; 
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_add(v_i_582_, v___x_586_);
v_i_582_ = v___x_587_;
v_b_583_ = v_a_585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_608_, lean_object* v_sz_609_, lean_object* v_i_610_, lean_object* v_b_611_){
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_609_);
lean_dec(v_sz_609_);
v_i_boxed_613_ = lean_unbox_usize(v_i_610_);
lean_dec(v_i_610_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_as_608_, v_sz_boxed_612_, v_i_boxed_613_, v_b_611_);
lean_dec_ref(v_as_608_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_615_, lean_object* v_k_616_, uint8_t v_v_617_){
_start:
{
lean_object* v_map_618_; uint8_t v_hasTrace_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_633_; 
v_map_618_ = lean_ctor_get(v_o_615_, 0);
v_hasTrace_619_ = lean_ctor_get_uint8(v_o_615_, sizeof(void*)*1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_o_615_);
if (v_isSharedCheck_633_ == 0)
{
v___x_621_ = v_o_615_;
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_map_618_);
lean_dec(v_o_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_623_, 0, v_v_617_);
lean_inc(v_k_616_);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_616_, v___x_623_, v_map_618_);
if (v_hasTrace_619_ == 0)
{
lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_628_; 
v___x_625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_626_ = l_Lean_Name_isPrefixOf(v___x_625_, v_k_616_);
lean_dec(v_k_616_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_624_);
v___x_628_ = v___x_621_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_624_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*1, v___x_626_);
return v___x_628_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v_k_616_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_624_);
v___x_631_ = v___x_621_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_624_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*1, v_hasTrace_619_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_634_, lean_object* v_k_635_, lean_object* v_v_636_){
_start:
{
uint8_t v_v_boxed_637_; lean_object* v_res_638_; 
v_v_boxed_637_ = lean_unbox(v_v_636_);
v_res_638_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_634_, v_k_635_, v_v_boxed_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_639_, lean_object* v_opt_640_, uint8_t v_val_641_){
_start:
{
lean_object* v_name_642_; lean_object* v___x_643_; 
v_name_642_ = lean_ctor_get(v_opt_640_, 0);
lean_inc(v_name_642_);
lean_dec_ref(v_opt_640_);
v___x_643_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_639_, v_name_642_, v_val_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_644_, lean_object* v_opt_645_, lean_object* v_val_646_){
_start:
{
uint8_t v_val_boxed_647_; lean_object* v_res_648_; 
v_val_boxed_647_ = lean_unbox(v_val_646_);
v_res_648_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_644_, v_opt_645_, v_val_boxed_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(lean_object* v_as_649_, size_t v_i_650_, size_t v_stop_651_, lean_object* v_b_652_){
_start:
{
uint8_t v___x_653_; 
v___x_653_ = lean_usize_dec_eq(v_i_650_, v_stop_651_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v_defValue_655_; uint8_t v___x_656_; lean_object* v___x_657_; size_t v___x_658_; size_t v___x_659_; 
v___x_654_ = lean_array_uget_borrowed(v_as_649_, v_i_650_);
v_defValue_655_ = lean_ctor_get(v___x_654_, 1);
v___x_656_ = lean_unbox(v_defValue_655_);
lean_inc(v___x_654_);
v___x_657_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_652_, v___x_654_, v___x_656_);
v___x_658_ = ((size_t)1ULL);
v___x_659_ = lean_usize_add(v_i_650_, v___x_658_);
v_i_650_ = v___x_659_;
v_b_652_ = v___x_657_;
goto _start;
}
else
{
return v_b_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(lean_object* v_as_661_, lean_object* v_i_662_, lean_object* v_stop_663_, lean_object* v_b_664_){
_start:
{
size_t v_i_boxed_665_; size_t v_stop_boxed_666_; lean_object* v_res_667_; 
v_i_boxed_665_ = lean_unbox_usize(v_i_662_);
lean_dec(v_i_662_);
v_stop_boxed_666_ = lean_unbox_usize(v_stop_663_);
lean_dec(v_stop_663_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v_as_661_, v_i_boxed_665_, v_stop_boxed_666_, v_b_664_);
lean_dec_ref(v_as_661_);
return v_res_667_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Array_instInhabited(lean_box(0));
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = l_Lean_Meta_eqnAffectingOptions;
v___x_675_ = lean_array_get_size(v___x_674_);
return v___x_675_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_nat_dec_lt(v___x_677_, v___x_676_);
return v___x_678_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_680_ = lean_nat_dec_le(v___x_679_, v___x_679_);
return v___x_680_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__7(void){
_start:
{
lean_object* v___x_681_; size_t v___x_682_; 
v___x_681_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_682_ = lean_usize_of_nat(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_683_, lean_object* v_act_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v_fileName_693_; lean_object* v_fileMap_694_; lean_object* v_currRecDepth_695_; lean_object* v_ref_696_; lean_object* v_currNamespace_697_; lean_object* v_openDecls_698_; lean_object* v_initHeartbeats_699_; lean_object* v_maxHeartbeats_700_; lean_object* v_quotContext_701_; lean_object* v_currMacroScope_702_; lean_object* v_cancelTk_x3f_703_; uint8_t v_suppressElabErrors_704_; lean_object* v_inheritedTraceOptions_705_; lean_object* v___y_706_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_env_713_; lean_object* v___x_714_; lean_object* v_toEnvExtension_715_; lean_object* v_asyncMode_716_; lean_object* v_fileName_717_; lean_object* v_fileMap_718_; lean_object* v_options_719_; lean_object* v_currRecDepth_720_; lean_object* v_ref_721_; lean_object* v_currNamespace_722_; lean_object* v_openDecls_723_; lean_object* v_initHeartbeats_724_; lean_object* v_maxHeartbeats_725_; lean_object* v_quotContext_726_; lean_object* v_currMacroScope_727_; lean_object* v_cancelTk_x3f_728_; uint8_t v_suppressElabErrors_729_; lean_object* v_inheritedTraceOptions_730_; uint8_t v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; lean_object* v___y_756_; lean_object* v___x_761_; uint8_t v___x_762_; lean_object* v___x_763_; 
v___x_711_ = lean_st_ref_get(v_a_688_);
v___x_712_ = lean_st_ref_get(v_a_688_);
v_env_713_ = lean_ctor_get(v___x_711_, 0);
lean_inc_ref(v_env_713_);
lean_dec(v___x_711_);
v___x_714_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_715_ = lean_ctor_get(v___x_714_, 0);
v_asyncMode_716_ = lean_ctor_get(v_toEnvExtension_715_, 2);
v_fileName_717_ = lean_ctor_get(v_a_687_, 0);
v_fileMap_718_ = lean_ctor_get(v_a_687_, 1);
v_options_719_ = lean_ctor_get(v_a_687_, 2);
v_currRecDepth_720_ = lean_ctor_get(v_a_687_, 3);
v_ref_721_ = lean_ctor_get(v_a_687_, 5);
v_currNamespace_722_ = lean_ctor_get(v_a_687_, 6);
v_openDecls_723_ = lean_ctor_get(v_a_687_, 7);
v_initHeartbeats_724_ = lean_ctor_get(v_a_687_, 8);
v_maxHeartbeats_725_ = lean_ctor_get(v_a_687_, 9);
v_quotContext_726_ = lean_ctor_get(v_a_687_, 10);
v_currMacroScope_727_ = lean_ctor_get(v_a_687_, 11);
v_cancelTk_x3f_728_ = lean_ctor_get(v_a_687_, 12);
v_suppressElabErrors_729_ = lean_ctor_get_uint8(v_a_687_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_730_ = lean_ctor_get(v_a_687_, 13);
v___x_761_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_762_ = 0;
v___x_763_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_761_, v___x_714_, v_env_713_, v_declName_683_, v_asyncMode_716_, v___x_762_);
if (lean_obj_tag(v___x_763_) == 1)
{
lean_object* v_val_764_; lean_object* v___y_766_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_val_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_val_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_770_ = l_Lean_Meta_eqnAffectingOptions;
v___x_771_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_771_ == 0)
{
lean_inc_ref(v_options_719_);
v___y_766_ = v_options_719_;
goto v___jp_765_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_772_ == 0)
{
if (v___x_771_ == 0)
{
lean_inc_ref(v_options_719_);
v___y_766_ = v_options_719_;
goto v___jp_765_;
}
else
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
v___x_773_ = ((size_t)0ULL);
v___x_774_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_719_);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_770_, v___x_773_, v___x_774_, v_options_719_);
v___y_766_ = v___x_775_;
goto v___jp_765_;
}
}
else
{
size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((size_t)0ULL);
v___x_777_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_719_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_770_, v___x_776_, v___x_777_, v_options_719_);
v___y_766_ = v___x_778_;
goto v___jp_765_;
}
}
v___jp_765_:
{
size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; 
v_sz_767_ = lean_array_size(v_val_764_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_764_, v_sz_767_, v___x_768_, v___y_766_);
lean_dec(v_val_764_);
v___y_756_ = v___x_769_;
goto v___jp_755_;
}
}
else
{
lean_object* v___x_779_; uint8_t v___x_780_; 
lean_dec(v___x_763_);
v___x_779_ = l_Lean_Meta_eqnAffectingOptions;
v___x_780_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_780_ == 0)
{
lean_inc_ref(v_options_719_);
v___y_756_ = v_options_719_;
goto v___jp_755_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_781_ == 0)
{
if (v___x_780_ == 0)
{
lean_inc_ref(v_options_719_);
v___y_756_ = v_options_719_;
goto v___jp_755_;
}
else
{
size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((size_t)0ULL);
v___x_783_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_719_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_779_, v___x_782_, v___x_783_, v_options_719_);
v___y_756_ = v___x_784_;
goto v___jp_755_;
}
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_719_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_779_, v___x_785_, v___x_786_, v_options_719_);
v___y_756_ = v___x_787_;
goto v___jp_755_;
}
}
}
v___jp_690_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_707_ = l_Lean_maxRecDepth;
v___x_708_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_692_, v___x_707_);
lean_inc_ref(v_inheritedTraceOptions_705_);
lean_inc(v_cancelTk_x3f_703_);
lean_inc(v_currMacroScope_702_);
lean_inc(v_quotContext_701_);
lean_inc(v_maxHeartbeats_700_);
lean_inc(v_initHeartbeats_699_);
lean_inc(v_openDecls_698_);
lean_inc(v_currNamespace_697_);
lean_inc(v_ref_696_);
lean_inc(v_currRecDepth_695_);
lean_inc_ref(v_fileMap_694_);
lean_inc_ref(v_fileName_693_);
v___x_709_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_709_, 0, v_fileName_693_);
lean_ctor_set(v___x_709_, 1, v_fileMap_694_);
lean_ctor_set(v___x_709_, 2, v___y_692_);
lean_ctor_set(v___x_709_, 3, v_currRecDepth_695_);
lean_ctor_set(v___x_709_, 4, v___x_708_);
lean_ctor_set(v___x_709_, 5, v_ref_696_);
lean_ctor_set(v___x_709_, 6, v_currNamespace_697_);
lean_ctor_set(v___x_709_, 7, v_openDecls_698_);
lean_ctor_set(v___x_709_, 8, v_initHeartbeats_699_);
lean_ctor_set(v___x_709_, 9, v_maxHeartbeats_700_);
lean_ctor_set(v___x_709_, 10, v_quotContext_701_);
lean_ctor_set(v___x_709_, 11, v_currMacroScope_702_);
lean_ctor_set(v___x_709_, 12, v_cancelTk_x3f_703_);
lean_ctor_set(v___x_709_, 13, v_inheritedTraceOptions_705_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*14, v___y_691_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*14 + 1, v_suppressElabErrors_704_);
lean_inc(v___y_706_);
lean_inc(v_a_686_);
lean_inc_ref(v_a_685_);
v___x_710_ = lean_apply_5(v_act_684_, v_a_685_, v_a_686_, v___x_709_, v___y_706_, lean_box(0));
return v___x_710_;
}
v___jp_731_:
{
if (v___y_734_ == 0)
{
lean_object* v___x_735_; lean_object* v_env_736_; lean_object* v_nextMacroScope_737_; lean_object* v_ngen_738_; lean_object* v_auxDeclNGen_739_; lean_object* v_traceState_740_; lean_object* v_messages_741_; lean_object* v_infoState_742_; lean_object* v_snapshotTasks_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_753_; 
v___x_735_ = lean_st_ref_take(v_a_688_);
v_env_736_ = lean_ctor_get(v___x_735_, 0);
v_nextMacroScope_737_ = lean_ctor_get(v___x_735_, 1);
v_ngen_738_ = lean_ctor_get(v___x_735_, 2);
v_auxDeclNGen_739_ = lean_ctor_get(v___x_735_, 3);
v_traceState_740_ = lean_ctor_get(v___x_735_, 4);
v_messages_741_ = lean_ctor_get(v___x_735_, 6);
v_infoState_742_ = lean_ctor_get(v___x_735_, 7);
v_snapshotTasks_743_ = lean_ctor_get(v___x_735_, 8);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v___x_735_, 5);
lean_dec(v_unused_754_);
v___x_745_ = v___x_735_;
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snapshotTasks_743_);
lean_inc(v_infoState_742_);
lean_inc(v_messages_741_);
lean_inc(v_traceState_740_);
lean_inc(v_auxDeclNGen_739_);
lean_inc(v_ngen_738_);
lean_inc(v_nextMacroScope_737_);
lean_inc(v_env_736_);
lean_dec(v___x_735_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = l_Lean_Kernel_enableDiag(v_env_736_, v___y_732_);
v___x_748_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 5, v___x_748_);
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_750_ = v___x_745_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_nextMacroScope_737_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_ngen_738_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_auxDeclNGen_739_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_traceState_740_);
lean_ctor_set(v_reuseFailAlloc_752_, 5, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_752_, 6, v_messages_741_);
lean_ctor_set(v_reuseFailAlloc_752_, 7, v_infoState_742_);
lean_ctor_set(v_reuseFailAlloc_752_, 8, v_snapshotTasks_743_);
v___x_750_ = v_reuseFailAlloc_752_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; 
v___x_751_ = lean_st_ref_set(v_a_688_, v___x_750_);
v___y_691_ = v___y_732_;
v___y_692_ = v___y_733_;
v_fileName_693_ = v_fileName_717_;
v_fileMap_694_ = v_fileMap_718_;
v_currRecDepth_695_ = v_currRecDepth_720_;
v_ref_696_ = v_ref_721_;
v_currNamespace_697_ = v_currNamespace_722_;
v_openDecls_698_ = v_openDecls_723_;
v_initHeartbeats_699_ = v_initHeartbeats_724_;
v_maxHeartbeats_700_ = v_maxHeartbeats_725_;
v_quotContext_701_ = v_quotContext_726_;
v_currMacroScope_702_ = v_currMacroScope_727_;
v_cancelTk_x3f_703_ = v_cancelTk_x3f_728_;
v_suppressElabErrors_704_ = v_suppressElabErrors_729_;
v_inheritedTraceOptions_705_ = v_inheritedTraceOptions_730_;
v___y_706_ = v_a_688_;
goto v___jp_690_;
}
}
}
else
{
v___y_691_ = v___y_732_;
v___y_692_ = v___y_733_;
v_fileName_693_ = v_fileName_717_;
v_fileMap_694_ = v_fileMap_718_;
v_currRecDepth_695_ = v_currRecDepth_720_;
v_ref_696_ = v_ref_721_;
v_currNamespace_697_ = v_currNamespace_722_;
v_openDecls_698_ = v_openDecls_723_;
v_initHeartbeats_699_ = v_initHeartbeats_724_;
v_maxHeartbeats_700_ = v_maxHeartbeats_725_;
v_quotContext_701_ = v_quotContext_726_;
v_currMacroScope_702_ = v_currMacroScope_727_;
v_cancelTk_x3f_703_ = v_cancelTk_x3f_728_;
v_suppressElabErrors_704_ = v_suppressElabErrors_729_;
v_inheritedTraceOptions_705_ = v_inheritedTraceOptions_730_;
v___y_706_ = v_a_688_;
goto v___jp_690_;
}
}
v___jp_755_:
{
lean_object* v_env_757_; lean_object* v___x_758_; uint8_t v___x_759_; uint8_t v___x_760_; 
v_env_757_ = lean_ctor_get(v___x_712_, 0);
lean_inc_ref(v_env_757_);
lean_dec(v___x_712_);
v___x_758_ = l_Lean_diagnostics;
v___x_759_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_756_, v___x_758_);
v___x_760_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_757_);
lean_dec_ref(v_env_757_);
if (v___x_760_ == 0)
{
if (v___x_759_ == 0)
{
v___y_691_ = v___x_759_;
v___y_692_ = v___y_756_;
v_fileName_693_ = v_fileName_717_;
v_fileMap_694_ = v_fileMap_718_;
v_currRecDepth_695_ = v_currRecDepth_720_;
v_ref_696_ = v_ref_721_;
v_currNamespace_697_ = v_currNamespace_722_;
v_openDecls_698_ = v_openDecls_723_;
v_initHeartbeats_699_ = v_initHeartbeats_724_;
v_maxHeartbeats_700_ = v_maxHeartbeats_725_;
v_quotContext_701_ = v_quotContext_726_;
v_currMacroScope_702_ = v_currMacroScope_727_;
v_cancelTk_x3f_703_ = v_cancelTk_x3f_728_;
v_suppressElabErrors_704_ = v_suppressElabErrors_729_;
v_inheritedTraceOptions_705_ = v_inheritedTraceOptions_730_;
v___y_706_ = v_a_688_;
goto v___jp_690_;
}
else
{
v___y_732_ = v___x_759_;
v___y_733_ = v___y_756_;
v___y_734_ = v___x_760_;
goto v___jp_731_;
}
}
else
{
v___y_732_ = v___x_759_;
v___y_733_ = v___y_756_;
v___y_734_ = v___x_759_;
goto v___jp_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_788_, lean_object* v_act_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_788_, v_act_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_796_, lean_object* v_declName_797_, lean_object* v_act_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_797_, v_act_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_805_, lean_object* v_declName_806_, lean_object* v_act_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_805_, v_declName_806_, v_act_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_env_818_; lean_object* v_toConstantVal_819_; lean_object* v_value_820_; lean_object* v_all_821_; uint8_t v___y_823_; lean_object* v_type_831_; uint8_t v___x_832_; 
v___x_817_ = lean_st_ref_get(v___y_815_);
v_env_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc_ref_n(v_env_818_, 2);
lean_dec(v___x_817_);
v_toConstantVal_819_ = lean_ctor_get(v_thm_814_, 0);
v_value_820_ = lean_ctor_get(v_thm_814_, 1);
v_all_821_ = lean_ctor_get(v_thm_814_, 2);
v_type_831_ = lean_ctor_get(v_toConstantVal_819_, 2);
v___x_832_ = l_Lean_Environment_hasUnsafe(v_env_818_, v_type_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_Environment_hasUnsafe(v_env_818_, v_value_820_);
v___y_823_ = v___x_833_;
goto v___jp_822_;
}
else
{
lean_dec_ref(v_env_818_);
v___y_823_ = v___x_832_;
goto v___jp_822_;
}
v___jp_822_:
{
if (v___y_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_824_, 0, v_thm_814_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_inc(v_all_821_);
lean_inc_ref(v_value_820_);
lean_inc_ref(v_toConstantVal_819_);
lean_dec_ref(v_thm_814_);
v___x_826_ = lean_box(0);
v___x_827_ = 0;
v___x_828_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_828_, 0, v_toConstantVal_819_);
lean_ctor_set(v___x_828_, 1, v_value_820_);
lean_ctor_set(v___x_828_, 2, v___x_826_);
lean_ctor_set(v___x_828_, 3, v_all_821_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*4, v___x_827_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_834_, v___y_835_);
lean_dec(v___y_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_838_, v___y_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_852_, lean_object* v_b_853_, lean_object* v_c_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
v___x_860_ = lean_apply_7(v_k_852_, v_b_853_, v_c_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_861_, lean_object* v_b_862_, lean_object* v_c_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_861_, v_b_862_, v_c_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_870_, lean_object* v_k_871_, uint8_t v_cleanupAnnotations_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___f_878_; uint8_t v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___f_878_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_878_, 0, v_k_871_);
v___x_879_ = 1;
v___x_880_ = 0;
v___x_881_ = lean_box(0);
v___x_882_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_870_, v___x_879_, v___x_880_, v___x_879_, v___x_880_, v___x_881_, v___f_878_, v_cleanupAnnotations_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
v_a_891_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_882_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_882_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_899_, lean_object* v_k_900_, lean_object* v_cleanupAnnotations_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_907_; lean_object* v_res_908_; 
v_cleanupAnnotations_boxed_907_ = lean_unbox(v_cleanupAnnotations_901_);
v_res_908_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_899_, v_k_900_, v_cleanupAnnotations_boxed_907_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_909_, lean_object* v_e_910_, lean_object* v_k_911_, uint8_t v_cleanupAnnotations_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_910_, v_k_911_, v_cleanupAnnotations_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_919_, lean_object* v_e_920_, lean_object* v_k_921_, lean_object* v_cleanupAnnotations_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_928_; lean_object* v_res_929_; 
v_cleanupAnnotations_boxed_928_ = lean_unbox(v_cleanupAnnotations_922_);
v_res_929_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_919_, v_e_920_, v_k_921_, v_cleanupAnnotations_boxed_928_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
if (lean_obj_tag(v_a_930_) == 0)
{
lean_object* v___x_932_; 
v___x_932_ = l_List_reverse___redArg(v_a_931_);
return v___x_932_;
}
else
{
lean_object* v_head_933_; lean_object* v_tail_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_943_; 
v_head_933_ = lean_ctor_get(v_a_930_, 0);
v_tail_934_ = lean_ctor_get(v_a_930_, 1);
v_isSharedCheck_943_ = !lean_is_exclusive(v_a_930_);
if (v_isSharedCheck_943_ == 0)
{
v___x_936_ = v_a_930_;
v_isShared_937_ = v_isSharedCheck_943_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_tail_934_);
lean_inc(v_head_933_);
lean_dec(v_a_930_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_943_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = l_Lean_mkLevelParam(v_head_933_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v_a_931_);
lean_ctor_set(v___x_936_, 0, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_a_931_);
v___x_940_ = v_reuseFailAlloc_942_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
v_a_930_ = v_tail_934_;
v_a_931_ = v___x_940_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_944_, lean_object* v_name_945_, lean_object* v_xs_946_, lean_object* v_body_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_name_953_; lean_object* v_levelParams_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1024_; 
v_name_953_ = lean_ctor_get(v_toConstantVal_944_, 0);
v_levelParams_954_ = lean_ctor_get(v_toConstantVal_944_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_toConstantVal_944_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v_toConstantVal_944_, 2);
lean_dec(v_unused_1025_);
v___x_956_ = v_toConstantVal_944_;
v_isShared_957_ = v_isSharedCheck_1024_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_levelParams_954_);
lean_inc(v_name_953_);
lean_dec(v_toConstantVal_944_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1024_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_lhs_961_; lean_object* v___x_962_; 
v___x_958_ = lean_box(0);
lean_inc(v_levelParams_954_);
v___x_959_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_954_, v___x_958_);
v___x_960_ = l_Lean_mkConst(v_name_953_, v___x_959_);
v_lhs_961_ = l_Lean_mkAppN(v___x_960_, v_xs_946_);
lean_inc_ref(v_lhs_961_);
v___x_962_ = l_Lean_Meta_mkEq(v_lhs_961_, v_body_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; uint8_t v___x_964_; uint8_t v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = 0;
v___x_965_ = 1;
v___x_966_ = 1;
v___x_967_ = l_Lean_Meta_mkForallFVars(v_xs_946_, v_a_963_, v___x_964_, v___x_965_, v___x_965_, v___x_966_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = l_Lean_Meta_letToHave(v_a_968_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_Meta_mkEqRefl(v_lhs_961_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_Meta_mkLambdaFVars(v_xs_946_, v_a_972_, v___x_964_, v___x_965_, v___x_964_, v___x_965_, v___x_966_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
lean_inc(v_name_945_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 2, v_a_970_);
lean_ctor_set(v___x_956_, 0, v_name_945_);
v___x_976_ = v___x_956_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_name_945_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_levelParams_954_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_a_970_);
v___x_976_ = v_reuseFailAlloc_983_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___x_981_; 
lean_inc(v_name_945_);
v___x_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_977_, 0, v_name_945_);
lean_ctor_set(v___x_977_, 1, v___x_958_);
v___x_978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v_a_974_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v___x_979_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_978_, v___y_951_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = l_Lean_addDecl(v_a_980_, v___x_964_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; 
lean_dec_ref_known(v___x_981_, 1);
v___x_982_ = l_Lean_inferDefEqAttr(v_name_945_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_982_;
}
else
{
lean_dec(v_name_945_);
return v___x_981_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_a_970_);
lean_del_object(v___x_956_);
lean_dec(v_levelParams_954_);
lean_dec(v_name_945_);
v_a_984_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_973_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_973_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v_a_970_);
lean_del_object(v___x_956_);
lean_dec(v_levelParams_954_);
lean_dec(v_name_945_);
v_a_992_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_971_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_971_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_lhs_961_);
lean_del_object(v___x_956_);
lean_dec(v_levelParams_954_);
lean_dec(v_name_945_);
v_a_1000_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_969_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_969_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_lhs_961_);
lean_del_object(v___x_956_);
lean_dec(v_levelParams_954_);
lean_dec(v_name_945_);
v_a_1008_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_967_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_967_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v_lhs_961_);
lean_del_object(v___x_956_);
lean_dec(v_levelParams_954_);
lean_dec(v_name_945_);
v_a_1016_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_962_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_962_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1026_, lean_object* v_name_1027_, lean_object* v_xs_1028_, lean_object* v_body_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1026_, v_name_1027_, v_xs_1028_, v_body_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v_xs_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1036_, lean_object* v_info_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_toConstantVal_1043_; lean_object* v_value_1044_; lean_object* v___f_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; 
v_toConstantVal_1043_ = lean_ctor_get(v_info_1037_, 0);
lean_inc_ref(v_toConstantVal_1043_);
v_value_1044_ = lean_ctor_get(v_info_1037_, 1);
lean_inc_ref(v_value_1044_);
lean_dec_ref(v_info_1037_);
v___f_1045_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1045_, 0, v_toConstantVal_1043_);
lean_closure_set(v___f_1045_, 1, v_name_1036_);
v___x_1046_ = 1;
v___x_1047_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1044_, v___f_1045_, v___x_1046_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1048_, lean_object* v_info_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1048_, v_info_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1056_, lean_object* v_name_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1066_; lean_object* v_env_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; 
v___x_1066_ = lean_st_ref_get(v_a_1061_);
v_env_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc_ref(v_env_1067_);
lean_dec(v___x_1066_);
v___x_1068_ = 0;
lean_inc(v_declName_1056_);
v___x_1069_ = l_Lean_Environment_find_x3f(v_env_1067_, v_declName_1056_, v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 1)
{
lean_object* v_val_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1097_; 
v_val_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1097_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_val_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1097_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
if (lean_obj_tag(v_val_1070_) == 1)
{
lean_object* v_val_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_val_1074_ = lean_ctor_get(v_val_1070_, 0);
lean_inc_ref(v_val_1074_);
lean_dec_ref_known(v_val_1070_, 1);
lean_inc_n(v_name_1057_, 2);
v___x_1075_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1075_, 0, v_name_1057_);
lean_closure_set(v___x_1075_, 1, v_val_1074_);
lean_inc(v_declName_1056_);
v___x_1076_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1076_, 0, lean_box(0));
lean_closure_set(v___x_1076_, 1, v_declName_1056_);
lean_closure_set(v___x_1076_, 2, v___x_1075_);
v___x_1077_ = l_Lean_Meta_realizeConst(v_declName_1056_, v_name_1057_, v___x_1076_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1087_; 
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v___x_1077_, 0);
lean_dec(v_unused_1088_);
v___x_1079_ = v___x_1077_;
v_isShared_1080_ = v_isSharedCheck_1087_;
goto v_resetjp_1078_;
}
else
{
lean_dec(v___x_1077_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1087_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v_name_1057_);
v___x_1082_ = v___x_1072_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_name_1057_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1082_);
v___x_1084_ = v___x_1079_;
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
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_del_object(v___x_1072_);
lean_dec(v_name_1057_);
v_a_1089_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1077_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1077_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_del_object(v___x_1072_);
lean_dec(v_val_1070_);
lean_dec(v_name_1057_);
lean_dec(v_declName_1056_);
goto v___jp_1063_;
}
}
}
else
{
lean_dec(v___x_1069_);
lean_dec(v_name_1057_);
lean_dec(v_declName_1056_);
goto v___jp_1063_;
}
v___jp_1063_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1098_, lean_object* v_name_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1098_, v_name_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1106_, lean_object* v_vals_1107_, lean_object* v_i_1108_, lean_object* v_k_1109_){
_start:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_array_get_size(v_keys_1106_);
v___x_1111_ = lean_nat_dec_lt(v_i_1108_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_i_1108_);
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
else
{
lean_object* v_k_x27_1113_; uint8_t v___x_1114_; 
v_k_x27_1113_ = lean_array_fget_borrowed(v_keys_1106_, v_i_1108_);
v___x_1114_ = lean_name_eq(v_k_1109_, v_k_x27_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_add(v_i_1108_, v___x_1115_);
lean_dec(v_i_1108_);
v_i_1108_ = v___x_1116_;
goto _start;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_array_fget_borrowed(v_vals_1107_, v_i_1108_);
lean_dec(v_i_1108_);
lean_inc(v___x_1118_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1120_, lean_object* v_vals_1121_, lean_object* v_i_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1120_, v_vals_1121_, v_i_1122_, v_k_1123_);
lean_dec(v_k_1123_);
lean_dec_ref(v_vals_1121_);
lean_dec_ref(v_keys_1120_);
return v_res_1124_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1125_; size_t v___x_1126_; size_t v___x_1127_; 
v___x_1125_ = ((size_t)5ULL);
v___x_1126_ = ((size_t)1ULL);
v___x_1127_ = lean_usize_shift_left(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1128_; size_t v___x_1129_; size_t v___x_1130_; 
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_1130_ = lean_usize_sub(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1131_, size_t v_x_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v_es_1134_; lean_object* v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; lean_object* v_j_1139_; lean_object* v___x_1140_; 
v_es_1134_ = lean_ctor_get(v_x_1131_, 0);
v___x_1135_ = lean_box(2);
v___x_1136_ = ((size_t)5ULL);
v___x_1137_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1138_ = lean_usize_land(v_x_1132_, v___x_1137_);
v_j_1139_ = lean_usize_to_nat(v___x_1138_);
v___x_1140_ = lean_array_get_borrowed(v___x_1135_, v_es_1134_, v_j_1139_);
lean_dec(v_j_1139_);
switch(lean_obj_tag(v___x_1140_))
{
case 0:
{
lean_object* v_key_1141_; lean_object* v_val_1142_; uint8_t v___x_1143_; 
v_key_1141_ = lean_ctor_get(v___x_1140_, 0);
v_val_1142_ = lean_ctor_get(v___x_1140_, 1);
v___x_1143_ = lean_name_eq(v_x_1133_, v_key_1141_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; 
lean_inc(v_val_1142_);
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_val_1142_);
return v___x_1145_;
}
}
case 1:
{
lean_object* v_node_1146_; size_t v___x_1147_; 
v_node_1146_ = lean_ctor_get(v___x_1140_, 0);
v___x_1147_ = lean_usize_shift_right(v_x_1132_, v___x_1136_);
v_x_1131_ = v_node_1146_;
v_x_1132_ = v___x_1147_;
goto _start;
}
default: 
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_box(0);
return v___x_1149_;
}
}
}
else
{
lean_object* v_ks_1150_; lean_object* v_vs_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_ks_1150_ = lean_ctor_get(v_x_1131_, 0);
v_vs_1151_ = lean_ctor_get(v_x_1131_, 1);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1150_, v_vs_1151_, v___x_1152_, v_x_1133_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
size_t v_x_355__boxed_1157_; lean_object* v_res_1158_; 
v_x_355__boxed_1157_ = lean_unbox_usize(v_x_1155_);
lean_dec(v_x_1155_);
v_res_1158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1154_, v_x_355__boxed_1157_, v_x_1156_);
lean_dec(v_x_1156_);
lean_dec_ref(v_x_1154_);
return v_res_1158_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1159_; uint64_t v___x_1160_; 
v___x_1159_ = lean_unsigned_to_nat(1723u);
v___x_1160_ = lean_uint64_of_nat(v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
uint64_t v___y_1164_; 
if (lean_obj_tag(v_x_1162_) == 0)
{
uint64_t v___x_1167_; 
v___x_1167_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1164_ = v___x_1167_;
goto v___jp_1163_;
}
else
{
uint64_t v_hash_1168_; 
v_hash_1168_ = lean_ctor_get_uint64(v_x_1162_, sizeof(void*)*2);
v___y_1164_ = v_hash_1168_;
goto v___jp_1163_;
}
v___jp_1163_:
{
size_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_uint64_to_usize(v___y_1164_);
v___x_1166_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1161_, v___x_1165_, v_x_1162_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1169_, v_x_1170_);
lean_dec(v_x_1170_);
lean_dec_ref(v_x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v_env_1176_; lean_object* v___x_1177_; lean_object* v_asyncMode_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1175_ = lean_st_ref_get(v_a_1173_);
v_env_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc_ref(v_env_1176_);
lean_dec(v___x_1175_);
v___x_1177_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1178_ = lean_ctor_get(v___x_1177_, 2);
v___x_1179_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1180_ = lean_box(0);
v___x_1181_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1179_, v___x_1177_, v_env_1176_, v_asyncMode_1178_, v___x_1180_);
v___x_1182_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1181_, v_thmName_1172_);
lean_dec(v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec(v_thmName_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1188_, v_a_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_thmName_1193_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1199_, v_x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1202_, lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1202_, v_x_1203_, v_x_1204_);
lean_dec(v_x_1204_);
lean_dec_ref(v_x_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1206_, lean_object* v_x_1207_, size_t v_x_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1207_, v_x_1208_, v_x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_, lean_object* v_x_1214_){
_start:
{
size_t v_x_460__boxed_1215_; lean_object* v_res_1216_; 
v_x_460__boxed_1215_ = lean_unbox_usize(v_x_1213_);
lean_dec(v_x_1213_);
v_res_1216_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1211_, v_x_1212_, v_x_460__boxed_1215_, v_x_1214_);
lean_dec(v_x_1214_);
lean_dec_ref(v_x_1212_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1217_, lean_object* v_keys_1218_, lean_object* v_vals_1219_, lean_object* v_heq_1220_, lean_object* v_i_1221_, lean_object* v_k_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1218_, v_vals_1219_, v_i_1221_, v_k_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1224_, lean_object* v_keys_1225_, lean_object* v_vals_1226_, lean_object* v_heq_1227_, lean_object* v_i_1228_, lean_object* v_k_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1224_, v_keys_1225_, v_vals_1226_, v_heq_1227_, v_i_1228_, v_k_1229_);
lean_dec(v_k_1229_);
lean_dec_ref(v_vals_1226_);
lean_dec_ref(v_keys_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1231_, lean_object* v_i_1232_, lean_object* v_k_1233_){
_start:
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = lean_array_get_size(v_keys_1231_);
v___x_1235_ = lean_nat_dec_lt(v_i_1232_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec(v_i_1232_);
return v___x_1235_;
}
else
{
lean_object* v_k_x27_1236_; uint8_t v___x_1237_; 
v_k_x27_1236_ = lean_array_fget_borrowed(v_keys_1231_, v_i_1232_);
v___x_1237_ = lean_name_eq(v_k_1233_, v_k_x27_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_add(v_i_1232_, v___x_1238_);
lean_dec(v_i_1232_);
v_i_1232_ = v___x_1239_;
goto _start;
}
else
{
lean_dec(v_i_1232_);
return v___x_1237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1241_, lean_object* v_i_1242_, lean_object* v_k_1243_){
_start:
{
uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_res_1244_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1241_, v_i_1242_, v_k_1243_);
lean_dec(v_k_1243_);
lean_dec_ref(v_keys_1241_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1246_, size_t v_x_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v_es_1249_; lean_object* v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v_j_1254_; lean_object* v___x_1255_; 
v_es_1249_ = lean_ctor_get(v_x_1246_, 0);
v___x_1250_ = lean_box(2);
v___x_1251_ = ((size_t)5ULL);
v___x_1252_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1253_ = lean_usize_land(v_x_1247_, v___x_1252_);
v_j_1254_ = lean_usize_to_nat(v___x_1253_);
v___x_1255_ = lean_array_get_borrowed(v___x_1250_, v_es_1249_, v_j_1254_);
lean_dec(v_j_1254_);
switch(lean_obj_tag(v___x_1255_))
{
case 0:
{
lean_object* v_key_1256_; uint8_t v___x_1257_; 
v_key_1256_ = lean_ctor_get(v___x_1255_, 0);
v___x_1257_ = lean_name_eq(v_x_1248_, v_key_1256_);
return v___x_1257_;
}
case 1:
{
lean_object* v_node_1258_; size_t v___x_1259_; 
v_node_1258_ = lean_ctor_get(v___x_1255_, 0);
v___x_1259_ = lean_usize_shift_right(v_x_1247_, v___x_1251_);
v_x_1246_ = v_node_1258_;
v_x_1247_ = v___x_1259_;
goto _start;
}
default: 
{
uint8_t v___x_1261_; 
v___x_1261_ = 0;
return v___x_1261_;
}
}
}
else
{
lean_object* v_ks_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_ks_1262_ = lean_ctor_get(v_x_1246_, 0);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1262_, v___x_1263_, v_x_1248_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
size_t v_x_335__boxed_1268_; uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_x_335__boxed_1268_ = lean_unbox_usize(v_x_1266_);
lean_dec(v_x_1266_);
v_res_1269_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1265_, v_x_335__boxed_1268_, v_x_1267_);
lean_dec(v_x_1267_);
lean_dec_ref(v_x_1265_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
uint64_t v___y_1274_; 
if (lean_obj_tag(v_x_1272_) == 0)
{
uint64_t v___x_1277_; 
v___x_1277_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1274_ = v___x_1277_;
goto v___jp_1273_;
}
else
{
uint64_t v_hash_1278_; 
v_hash_1278_ = lean_ctor_get_uint64(v_x_1272_, sizeof(void*)*2);
v___y_1274_ = v_hash_1278_;
goto v___jp_1273_;
}
v___jp_1273_:
{
size_t v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_uint64_to_usize(v___y_1274_);
v___x_1276_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1271_, v___x_1275_, v_x_1272_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1279_, v_x_1280_);
lean_dec(v_x_1280_);
lean_dec_ref(v_x_1279_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1286_; lean_object* v_env_1287_; lean_object* v___x_1288_; lean_object* v_asyncMode_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1286_ = lean_st_ref_get(v_a_1284_);
v_env_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc_ref(v_env_1287_);
lean_dec(v___x_1286_);
v___x_1288_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1289_ = lean_ctor_get(v___x_1288_, 2);
v___x_1290_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1291_ = lean_box(0);
v___x_1292_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1290_, v___x_1288_, v_env_1287_, v_asyncMode_1289_, v___x_1291_);
v___x_1293_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1292_, v_thmName_1283_);
lean_dec(v___x_1292_);
v___x_1294_ = lean_box(v___x_1293_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec(v_thmName_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1300_, v_a_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_isEqnThm(v_thmName_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_thmName_1305_);
return v_res_1309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1311_, v_x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_res_1317_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1314_, v_x_1315_, v_x_1316_);
lean_dec(v_x_1316_);
lean_dec_ref(v_x_1315_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1319_, lean_object* v_x_1320_, size_t v_x_1321_, lean_object* v_x_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1320_, v_x_1321_, v_x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
size_t v_x_429__boxed_1328_; uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_x_429__boxed_1328_ = lean_unbox_usize(v_x_1326_);
lean_dec(v_x_1326_);
v_res_1329_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1324_, v_x_1325_, v_x_429__boxed_1328_, v_x_1327_);
lean_dec(v_x_1327_);
lean_dec_ref(v_x_1325_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1331_, lean_object* v_keys_1332_, lean_object* v_vals_1333_, lean_object* v_heq_1334_, lean_object* v_i_1335_, lean_object* v_k_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1332_, v_i_1335_, v_k_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1338_, lean_object* v_keys_1339_, lean_object* v_vals_1340_, lean_object* v_heq_1341_, lean_object* v_i_1342_, lean_object* v_k_1343_){
_start:
{
uint8_t v_res_1344_; lean_object* v_r_1345_; 
v_res_1344_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1338_, v_keys_1339_, v_vals_1340_, v_heq_1341_, v_i_1342_, v_k_1343_);
lean_dec(v_k_1343_);
lean_dec_ref(v_vals_1340_);
lean_dec_ref(v_keys_1339_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
lean_object* v_ks_1350_; lean_object* v_vs_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1375_; 
v_ks_1350_ = lean_ctor_get(v_x_1346_, 0);
v_vs_1351_ = lean_ctor_get(v_x_1346_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_x_1346_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1353_ = v_x_1346_;
v_isShared_1354_ = v_isSharedCheck_1375_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_vs_1351_);
lean_inc(v_ks_1350_);
lean_dec(v_x_1346_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1375_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_array_get_size(v_ks_1350_);
v___x_1356_ = lean_nat_dec_lt(v_x_1347_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_dec(v_x_1347_);
v___x_1357_ = lean_array_push(v_ks_1350_, v_x_1348_);
v___x_1358_ = lean_array_push(v_vs_1351_, v_x_1349_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1358_);
lean_ctor_set(v___x_1353_, 0, v___x_1357_);
v___x_1360_ = v___x_1353_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v_k_x27_1362_; uint8_t v___x_1363_; 
v_k_x27_1362_ = lean_array_fget_borrowed(v_ks_1350_, v_x_1347_);
v___x_1363_ = lean_name_eq(v_x_1348_, v_k_x27_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1365_; 
if (v_isShared_1354_ == 0)
{
v___x_1365_ = v___x_1353_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_ks_1350_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_vs_1351_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_add(v_x_1347_, v___x_1366_);
lean_dec(v_x_1347_);
v_x_1346_ = v___x_1365_;
v_x_1347_ = v___x_1367_;
goto _start;
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = lean_array_fset(v_ks_1350_, v_x_1347_, v_x_1348_);
v___x_1371_ = lean_array_fset(v_vs_1351_, v_x_1347_, v_x_1349_);
lean_dec(v_x_1347_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1371_);
lean_ctor_set(v___x_1353_, 0, v___x_1370_);
v___x_1373_ = v___x_1353_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1371_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1376_, lean_object* v_k_1377_, lean_object* v_v_1378_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1376_, v___x_1379_, v_k_1377_, v_v_1378_);
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1382_, size_t v_x_1383_, size_t v_x_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 0)
{
lean_object* v_es_1387_; size_t v___x_1388_; size_t v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; lean_object* v_j_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_es_1387_ = lean_ctor_get(v_x_1382_, 0);
v___x_1388_ = ((size_t)5ULL);
v___x_1389_ = ((size_t)1ULL);
v___x_1390_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1391_ = lean_usize_land(v_x_1383_, v___x_1390_);
v_j_1392_ = lean_usize_to_nat(v___x_1391_);
v___x_1393_ = lean_array_get_size(v_es_1387_);
v___x_1394_ = lean_nat_dec_lt(v_j_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_dec(v_j_1392_);
lean_dec(v_x_1386_);
lean_dec(v_x_1385_);
return v_x_1382_;
}
else
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1431_; 
lean_inc_ref(v_es_1387_);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1432_);
v___x_1396_ = v_x_1382_;
v_isShared_1397_ = v_isSharedCheck_1431_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v_x_1382_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1431_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_v_1398_; lean_object* v___x_1399_; lean_object* v_xs_x27_1400_; lean_object* v___y_1402_; 
v_v_1398_ = lean_array_fget(v_es_1387_, v_j_1392_);
v___x_1399_ = lean_box(0);
v_xs_x27_1400_ = lean_array_fset(v_es_1387_, v_j_1392_, v___x_1399_);
switch(lean_obj_tag(v_v_1398_))
{
case 0:
{
lean_object* v_key_1407_; lean_object* v_val_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1418_; 
v_key_1407_ = lean_ctor_get(v_v_1398_, 0);
v_val_1408_ = lean_ctor_get(v_v_1398_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_v_1398_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1410_ = v_v_1398_;
v_isShared_1411_ = v_isSharedCheck_1418_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_val_1408_);
lean_inc(v_key_1407_);
lean_dec(v_v_1398_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1418_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_name_eq(v_x_1385_, v_key_1407_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_del_object(v___x_1410_);
v___x_1413_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1407_, v_val_1408_, v_x_1385_, v_x_1386_);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
v___y_1402_ = v___x_1414_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1416_; 
lean_dec(v_val_1408_);
lean_dec(v_key_1407_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_x_1386_);
lean_ctor_set(v___x_1410_, 0, v_x_1385_);
v___x_1416_ = v___x_1410_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_x_1385_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_x_1386_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
v___y_1402_ = v___x_1416_;
goto v___jp_1401_;
}
}
}
}
case 1:
{
lean_object* v_node_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1429_; 
v_node_1419_ = lean_ctor_get(v_v_1398_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_v_1398_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1421_ = v_v_1398_;
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_node_1419_);
lean_dec(v_v_1398_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1423_ = lean_usize_shift_right(v_x_1383_, v___x_1388_);
v___x_1424_ = lean_usize_add(v_x_1384_, v___x_1389_);
v___x_1425_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1419_, v___x_1423_, v___x_1424_, v_x_1385_, v_x_1386_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1425_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
v___y_1402_ = v___x_1427_;
goto v___jp_1401_;
}
}
}
default: 
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_x_1385_);
lean_ctor_set(v___x_1430_, 1, v_x_1386_);
v___y_1402_ = v___x_1430_;
goto v___jp_1401_;
}
}
v___jp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_array_fset(v_xs_x27_1400_, v_j_1392_, v___y_1402_);
lean_dec(v_j_1392_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1403_);
v___x_1405_ = v___x_1396_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
lean_object* v_ks_1433_; lean_object* v_vs_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1454_; 
v_ks_1433_ = lean_ctor_get(v_x_1382_, 0);
v_vs_1434_ = lean_ctor_get(v_x_1382_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1436_ = v_x_1382_;
v_isShared_1437_ = v_isSharedCheck_1454_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_vs_1434_);
lean_inc(v_ks_1433_);
lean_dec(v_x_1382_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1454_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_ks_1433_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_vs_1434_);
v___x_1439_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v_newNode_1440_; uint8_t v___y_1442_; size_t v___x_1448_; uint8_t v___x_1449_; 
v_newNode_1440_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1439_, v_x_1385_, v_x_1386_);
v___x_1448_ = ((size_t)7ULL);
v___x_1449_ = lean_usize_dec_le(v___x_1448_, v_x_1384_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1440_);
v___x_1451_ = lean_unsigned_to_nat(4u);
v___x_1452_ = lean_nat_dec_lt(v___x_1450_, v___x_1451_);
lean_dec(v___x_1450_);
v___y_1442_ = v___x_1452_;
goto v___jp_1441_;
}
else
{
v___y_1442_ = v___x_1449_;
goto v___jp_1441_;
}
v___jp_1441_:
{
if (v___y_1442_ == 0)
{
lean_object* v_ks_1443_; lean_object* v_vs_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_ks_1443_ = lean_ctor_get(v_newNode_1440_, 0);
lean_inc_ref(v_ks_1443_);
v_vs_1444_ = lean_ctor_get(v_newNode_1440_, 1);
lean_inc_ref(v_vs_1444_);
lean_dec_ref(v_newNode_1440_);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1384_, v_ks_1443_, v_vs_1444_, v___x_1445_, v___x_1446_);
lean_dec_ref(v_vs_1444_);
lean_dec_ref(v_ks_1443_);
return v___x_1447_;
}
else
{
return v_newNode_1440_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1455_, lean_object* v_keys_1456_, lean_object* v_vals_1457_, lean_object* v_i_1458_, lean_object* v_entries_1459_){
_start:
{
lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = lean_array_get_size(v_keys_1456_);
v___x_1461_ = lean_nat_dec_lt(v_i_1458_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_dec(v_i_1458_);
return v_entries_1459_;
}
else
{
lean_object* v_k_1462_; lean_object* v_v_1463_; uint64_t v___y_1465_; 
v_k_1462_ = lean_array_fget_borrowed(v_keys_1456_, v_i_1458_);
v_v_1463_ = lean_array_fget_borrowed(v_vals_1457_, v_i_1458_);
if (lean_obj_tag(v_k_1462_) == 0)
{
uint64_t v___x_1476_; 
v___x_1476_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1465_ = v___x_1476_;
goto v___jp_1464_;
}
else
{
uint64_t v_hash_1477_; 
v_hash_1477_ = lean_ctor_get_uint64(v_k_1462_, sizeof(void*)*2);
v___y_1465_ = v_hash_1477_;
goto v___jp_1464_;
}
v___jp_1464_:
{
size_t v_h_1466_; size_t v___x_1467_; lean_object* v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; size_t v_h_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_h_1466_ = lean_uint64_to_usize(v___y_1465_);
v___x_1467_ = ((size_t)5ULL);
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = ((size_t)1ULL);
v___x_1470_ = lean_usize_sub(v_depth_1455_, v___x_1469_);
v___x_1471_ = lean_usize_mul(v___x_1467_, v___x_1470_);
v_h_1472_ = lean_usize_shift_right(v_h_1466_, v___x_1471_);
v___x_1473_ = lean_nat_add(v_i_1458_, v___x_1468_);
lean_dec(v_i_1458_);
lean_inc(v_v_1463_);
lean_inc(v_k_1462_);
v___x_1474_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1459_, v_h_1472_, v_depth_1455_, v_k_1462_, v_v_1463_);
v_i_1458_ = v___x_1473_;
v_entries_1459_ = v___x_1474_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1478_, lean_object* v_keys_1479_, lean_object* v_vals_1480_, lean_object* v_i_1481_, lean_object* v_entries_1482_){
_start:
{
size_t v_depth_boxed_1483_; lean_object* v_res_1484_; 
v_depth_boxed_1483_ = lean_unbox_usize(v_depth_1478_);
lean_dec(v_depth_1478_);
v_res_1484_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1483_, v_keys_1479_, v_vals_1480_, v_i_1481_, v_entries_1482_);
lean_dec_ref(v_vals_1480_);
lean_dec_ref(v_keys_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_){
_start:
{
size_t v_x_634__boxed_1490_; size_t v_x_635__boxed_1491_; lean_object* v_res_1492_; 
v_x_634__boxed_1490_ = lean_unbox_usize(v_x_1486_);
lean_dec(v_x_1486_);
v_x_635__boxed_1491_ = lean_unbox_usize(v_x_1487_);
lean_dec(v_x_1487_);
v_res_1492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1485_, v_x_634__boxed_1490_, v_x_635__boxed_1491_, v_x_1488_, v_x_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_){
_start:
{
uint64_t v___y_1497_; 
if (lean_obj_tag(v_x_1494_) == 0)
{
uint64_t v___x_1501_; 
v___x_1501_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1497_ = v___x_1501_;
goto v___jp_1496_;
}
else
{
uint64_t v_hash_1502_; 
v_hash_1502_ = lean_ctor_get_uint64(v_x_1494_, sizeof(void*)*2);
v___y_1497_ = v_hash_1502_;
goto v___jp_1496_;
}
v___jp_1496_:
{
size_t v___x_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_uint64_to_usize(v___y_1497_);
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1493_, v___x_1498_, v___x_1499_, v_x_1494_, v_x_1495_);
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1503_, lean_object* v_as_1504_, size_t v_i_1505_, size_t v_stop_1506_, lean_object* v_b_1507_){
_start:
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_usize_dec_eq(v_i_1505_, v_stop_1506_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; 
v___x_1509_ = lean_array_uget_borrowed(v_as_1504_, v_i_1505_);
lean_inc(v_declName_1503_);
lean_inc(v___x_1509_);
v___x_1510_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1507_, v___x_1509_, v_declName_1503_);
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1505_, v___x_1511_);
v_i_1505_ = v___x_1512_;
v_b_1507_ = v___x_1510_;
goto _start;
}
else
{
lean_dec(v_declName_1503_);
return v_b_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1514_, lean_object* v_as_1515_, lean_object* v_i_1516_, lean_object* v_stop_1517_, lean_object* v_b_1518_){
_start:
{
size_t v_i_boxed_1519_; size_t v_stop_boxed_1520_; lean_object* v_res_1521_; 
v_i_boxed_1519_ = lean_unbox_usize(v_i_1516_);
lean_dec(v_i_1516_);
v_stop_boxed_1520_ = lean_unbox_usize(v_stop_1517_);
lean_dec(v_stop_1517_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1514_, v_as_1515_, v_i_boxed_1519_, v_stop_boxed_1520_, v_b_1518_);
lean_dec_ref(v_as_1515_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1522_, lean_object* v_declName_1523_, lean_object* v_s_1524_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1525_ = lean_unsigned_to_nat(0u);
v___x_1526_ = lean_array_get_size(v_eqThms_1522_);
v___x_1527_ = lean_nat_dec_lt(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_dec(v_declName_1523_);
return v_s_1524_;
}
else
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_le(v___x_1526_, v___x_1526_);
if (v___x_1528_ == 0)
{
if (v___x_1527_ == 0)
{
lean_dec(v_declName_1523_);
return v_s_1524_;
}
else
{
size_t v___x_1529_; size_t v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = ((size_t)0ULL);
v___x_1530_ = lean_usize_of_nat(v___x_1526_);
v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1523_, v_eqThms_1522_, v___x_1529_, v___x_1530_, v_s_1524_);
return v___x_1531_;
}
}
else
{
size_t v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = lean_usize_of_nat(v___x_1526_);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1523_, v_eqThms_1522_, v___x_1532_, v___x_1533_, v_s_1524_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1535_, lean_object* v_declName_1536_, lean_object* v_s_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1535_, v_declName_1536_, v_s_1537_);
lean_dec_ref(v_eqThms_1535_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1539_, lean_object* v_eqThms_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v_env_1544_; lean_object* v_nextMacroScope_1545_; lean_object* v_ngen_1546_; lean_object* v_auxDeclNGen_1547_; lean_object* v_traceState_1548_; lean_object* v_messages_1549_; lean_object* v_infoState_1550_; lean_object* v_snapshotTasks_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1567_; 
v___x_1543_ = lean_st_ref_take(v_a_1541_);
v_env_1544_ = lean_ctor_get(v___x_1543_, 0);
v_nextMacroScope_1545_ = lean_ctor_get(v___x_1543_, 1);
v_ngen_1546_ = lean_ctor_get(v___x_1543_, 2);
v_auxDeclNGen_1547_ = lean_ctor_get(v___x_1543_, 3);
v_traceState_1548_ = lean_ctor_get(v___x_1543_, 4);
v_messages_1549_ = lean_ctor_get(v___x_1543_, 6);
v_infoState_1550_ = lean_ctor_get(v___x_1543_, 7);
v_snapshotTasks_1551_ = lean_ctor_get(v___x_1543_, 8);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v___x_1543_, 5);
lean_dec(v_unused_1568_);
v___x_1553_ = v___x_1543_;
v_isShared_1554_ = v_isSharedCheck_1567_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_snapshotTasks_1551_);
lean_inc(v_infoState_1550_);
lean_inc(v_messages_1549_);
lean_inc(v_traceState_1548_);
lean_inc(v_auxDeclNGen_1547_);
lean_inc(v_ngen_1546_);
lean_inc(v_nextMacroScope_1545_);
lean_inc(v_env_1544_);
lean_dec(v___x_1543_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1567_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v_asyncMode_1556_; lean_object* v___f_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1555_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1556_ = lean_ctor_get(v___x_1555_, 2);
v___f_1557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1557_, 0, v_eqThms_1540_);
lean_closure_set(v___f_1557_, 1, v_declName_1539_);
v___x_1558_ = lean_box(0);
v___x_1559_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1555_, v_env_1544_, v___f_1557_, v_asyncMode_1556_, v___x_1558_);
v___x_1560_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 5, v___x_1560_);
lean_ctor_set(v___x_1553_, 0, v___x_1559_);
v___x_1562_ = v___x_1553_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_nextMacroScope_1545_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_ngen_1546_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v_auxDeclNGen_1547_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v_traceState_1548_);
lean_ctor_set(v_reuseFailAlloc_1566_, 5, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1566_, 6, v_messages_1549_);
lean_ctor_set(v_reuseFailAlloc_1566_, 7, v_infoState_1550_);
lean_ctor_set(v_reuseFailAlloc_1566_, 8, v_snapshotTasks_1551_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_st_ref_set(v_a_1541_, v___x_1562_);
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1569_, lean_object* v_eqThms_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1569_, v_eqThms_1570_, v_a_1571_);
lean_dec(v_a_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1574_, lean_object* v_eqThms_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1574_, v_eqThms_1575_, v_a_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1580_, lean_object* v_eqThms_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1580_, v_eqThms_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1587_, v_x_1588_, v_x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1591_, lean_object* v_x_1592_, size_t v_x_1593_, size_t v_x_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1592_, v_x_1593_, v_x_1594_, v_x_1595_, v_x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
size_t v_x_903__boxed_1604_; size_t v_x_904__boxed_1605_; lean_object* v_res_1606_; 
v_x_903__boxed_1604_ = lean_unbox_usize(v_x_1600_);
lean_dec(v_x_1600_);
v_x_904__boxed_1605_ = lean_unbox_usize(v_x_1601_);
lean_dec(v_x_1601_);
v_res_1606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1598_, v_x_1599_, v_x_903__boxed_1604_, v_x_904__boxed_1605_, v_x_1602_, v_x_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1607_, lean_object* v_n_1608_, lean_object* v_k_1609_, lean_object* v_v_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1608_, v_k_1609_, v_v_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1612_, size_t v_depth_1613_, lean_object* v_keys_1614_, lean_object* v_vals_1615_, lean_object* v_heq_1616_, lean_object* v_i_1617_, lean_object* v_entries_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1613_, v_keys_1614_, v_vals_1615_, v_i_1617_, v_entries_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1620_, lean_object* v_depth_1621_, lean_object* v_keys_1622_, lean_object* v_vals_1623_, lean_object* v_heq_1624_, lean_object* v_i_1625_, lean_object* v_entries_1626_){
_start:
{
size_t v_depth_boxed_1627_; lean_object* v_res_1628_; 
v_depth_boxed_1627_ = lean_unbox_usize(v_depth_1621_);
lean_dec(v_depth_1621_);
v_res_1628_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1620_, v_depth_boxed_1627_, v_keys_1622_, v_vals_1623_, v_heq_1624_, v_i_1625_, v_entries_1626_);
lean_dec_ref(v_vals_1623_);
lean_dec_ref(v_keys_1622_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1630_, v_x_1631_, v_x_1632_, v_x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1635_, lean_object* v_env_1636_, lean_object* v_idx_1637_, lean_object* v_eqs_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_nextEq_1645_; uint8_t v___x_1646_; 
v___x_1640_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_nat_add(v_idx_1637_, v___x_1641_);
lean_dec(v_idx_1637_);
lean_inc(v___x_1642_);
v___x_1643_ = l_Nat_reprFast(v___x_1642_);
v___x_1644_ = lean_string_append(v___x_1640_, v___x_1643_);
lean_dec_ref(v___x_1643_);
lean_inc(v_declName_1635_);
lean_inc_ref(v_env_1636_);
v_nextEq_1645_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1636_, v_declName_1635_, v___x_1644_);
v___x_1646_ = l_Lean_Environment_containsOnBranch(v_env_1636_, v_nextEq_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_dec(v_nextEq_1645_);
lean_dec(v___x_1642_);
lean_dec_ref(v_env_1636_);
lean_dec(v_declName_1635_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_eqs_1638_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_array_push(v_eqs_1638_, v_nextEq_1645_);
v_idx_1637_ = v___x_1642_;
v_eqs_1638_ = v___x_1648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1650_, lean_object* v_env_1651_, lean_object* v_idx_1652_, lean_object* v_eqs_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1650_, v_env_1651_, v_idx_1652_, v_eqs_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1656_, lean_object* v_env_1657_, lean_object* v_idx_1658_, lean_object* v_eqs_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1656_, v_env_1657_, v_idx_1658_, v_eqs_1659_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1666_, lean_object* v_env_1667_, lean_object* v_idx_1668_, lean_object* v_eqs_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1666_, v_env_1667_, v_idx_1668_, v_eqs_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v_env_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; uint8_t v___x_1684_; 
v___x_1679_ = lean_st_ref_get(v_a_1677_);
v_env_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_ref_n(v_env_1680_, 3);
lean_dec(v___x_1679_);
v___x_1681_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1676_);
v___x_1682_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1680_, v_declName_1676_, v___x_1681_);
v___x_1683_ = 1;
lean_inc(v___x_1682_);
v___x_1684_ = l_Lean_Environment_contains(v_env_1680_, v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec(v___x_1682_);
lean_dec_ref(v_env_1680_);
lean_dec(v_declName_1676_);
v___x_1685_ = lean_box(0);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_mk_empty_array_with_capacity(v___x_1687_);
v___x_1689_ = lean_array_push(v___x_1688_, v___x_1682_);
lean_inc(v_declName_1676_);
v___x_1690_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1676_, v_env_1680_, v___x_1687_, v___x_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1700_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc_n(v_a_1691_, 2);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1676_, v_a_1691_, v_a_1677_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v___x_1692_, 0);
lean_dec(v_unused_1701_);
v___x_1694_ = v___x_1692_;
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v___x_1692_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1691_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1696_);
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_declName_1676_);
v_a_1702_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1690_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1690_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1710_, v_a_1711_);
lean_dec(v_a_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1714_, v_a_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1728_, lean_object* v_localInsts_1729_, lean_object* v_x_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1728_, v_localInsts_1729_, v_x_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
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
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1736_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1736_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1753_, lean_object* v_localInsts_1754_, lean_object* v_x_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1753_, v_localInsts_1754_, v_x_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1762_, lean_object* v_lctx_1763_, lean_object* v_localInsts_1764_, lean_object* v_x_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1763_, v_localInsts_1764_, v_x_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_lctx_1773_, lean_object* v_localInsts_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1772_, v_lctx_1773_, v_localInsts_1774_, v_x_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1785_, lean_object* v_as_x27_1786_, lean_object* v_b_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
if (lean_obj_tag(v_as_x27_1786_) == 0)
{
lean_object* v___x_1793_; 
lean_dec(v_declName_1785_);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v_b_1787_);
return v___x_1793_;
}
else
{
lean_object* v_head_1794_; lean_object* v_tail_1795_; lean_object* v___x_1796_; 
lean_dec_ref(v_b_1787_);
v_head_1794_ = lean_ctor_get(v_as_x27_1786_, 0);
v_tail_1795_ = lean_ctor_get(v_as_x27_1786_, 1);
lean_inc(v_head_1794_);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v_declName_1785_);
v___x_1796_ = lean_apply_6(v_head_1794_, v_declName_1785_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, lean_box(0));
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = lean_box(0);
if (lean_obj_tag(v_a_1797_) == 1)
{
lean_object* v_val_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1809_; 
v_val_1799_ = lean_ctor_get(v_a_1797_, 0);
lean_inc(v_val_1799_);
v___x_1800_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1785_, v_val_1799_, v___y_1791_);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v___x_1800_, 0);
lean_dec(v_unused_1810_);
v___x_1802_ = v___x_1800_;
v_isShared_1803_ = v_isSharedCheck_1809_;
goto v_resetjp_1801_;
}
else
{
lean_dec(v___x_1800_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1809_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_a_1797_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___x_1798_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1805_);
v___x_1807_ = v___x_1802_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
else
{
lean_object* v___x_1811_; 
lean_dec(v_a_1797_);
v___x_1811_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1786_ = v_tail_1795_;
v_b_1787_ = v___x_1811_;
goto _start;
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_declName_1785_);
v_a_1813_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1796_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1796_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1821_, lean_object* v_as_x27_1822_, lean_object* v_b_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1821_, v_as_x27_1822_, v_b_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v_as_x27_1822_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
lean_inc(v_declName_1830_);
v___x_1836_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1874_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1874_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1874_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_unbox(v_a_1837_);
lean_dec(v_a_1837_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_dec(v_declName_1830_);
v___x_1842_ = lean_box(0);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1842_);
v___x_1844_ = v___x_1839_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
else
{
lean_object* v___x_1846_; 
lean_del_object(v___x_1839_);
lean_inc(v_declName_1830_);
v___x_1846_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1830_, v___y_1834_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
if (lean_obj_tag(v_a_1847_) == 1)
{
lean_dec_ref_known(v_a_1847_, 1);
lean_dec(v_declName_1830_);
return v___x_1846_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1849_ = lean_st_ref_get(v___x_1848_);
v___x_1850_ = lean_box(0);
v___x_1851_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1852_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1830_, v___x_1849_, v___x_1851_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___x_1849_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1865_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1865_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1865_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_fst_1857_; 
v_fst_1857_ = lean_ctor_get(v_a_1853_, 0);
lean_inc(v_fst_1857_);
lean_dec(v_a_1853_);
if (lean_obj_tag(v_fst_1857_) == 0)
{
lean_object* v___x_1859_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1850_);
v___x_1859_ = v___x_1855_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1850_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_object* v_val_1861_; lean_object* v___x_1863_; 
v_val_1861_ = lean_ctor_get(v_fst_1857_, 0);
lean_inc(v_val_1861_);
lean_dec_ref_known(v_fst_1857_, 1);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_val_1861_);
v___x_1863_ = v___x_1855_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_val_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1852_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1852_);
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
}
else
{
lean_dec(v_declName_1830_);
return v___x_1846_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_declName_1830_);
v_a_1875_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1836_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1836_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1893_ = lean_box(1);
v___x_1894_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1895_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1894_);
lean_ctor_set(v___x_1896_, 2, v___x_1893_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___f_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___f_1905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1905_, 0, v_declName_1899_);
v___x_1906_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1907_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1908_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1906_, v___x_1907_, v___f_1905_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1916_, lean_object* v_as_1917_, lean_object* v_as_x27_1918_, lean_object* v_b_1919_, lean_object* v_a_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1916_, v_as_x27_1918_, v_b_1919_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1927_, lean_object* v_as_1928_, lean_object* v_as_x27_1929_, lean_object* v_b_1930_, lean_object* v_a_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1927_, v_as_1928_, v_as_x27_1929_, v_b_1930_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v_as_x27_1929_);
lean_dec(v_as_1928_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1944_ = lean_unsigned_to_nat(32u);
v___x_1945_ = lean_mk_empty_array_with_capacity(v___x_1944_);
lean_dec_ref(v___x_1945_);
v___x_1946_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1947_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1938_);
v___x_1948_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1948_, 0, v_declName_1938_);
v___x_1949_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1949_, 0, lean_box(0));
lean_closure_set(v___x_1949_, 1, v_declName_1938_);
lean_closure_set(v___x_1949_, 2, v___x_1948_);
v___x_1950_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1946_, v___x_1947_, v___x_1949_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; lean_object* v_env_1965_; lean_object* v___x_1966_; lean_object* v_mctx_1967_; lean_object* v_lctx_1968_; lean_object* v_options_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1964_ = lean_st_ref_get(v___y_1962_);
v_env_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc_ref(v_env_1965_);
lean_dec(v___x_1964_);
v___x_1966_ = lean_st_ref_get(v___y_1960_);
v_mctx_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc_ref(v_mctx_1967_);
lean_dec(v___x_1966_);
v_lctx_1968_ = lean_ctor_get(v___y_1959_, 2);
v_options_1969_ = lean_ctor_get(v___y_1961_, 2);
lean_inc_ref(v_options_1969_);
lean_inc_ref(v_lctx_1968_);
v___x_1970_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1970_, 0, v_env_1965_);
lean_ctor_set(v___x_1970_, 1, v_mctx_1967_);
lean_ctor_set(v___x_1970_, 2, v_lctx_1968_);
lean_ctor_set(v___x_1970_, 3, v_options_1969_);
v___x_1971_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v_msgData_1958_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1979_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1980_; double v___x_1981_; 
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = lean_float_of_nat(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1985_, lean_object* v_msg_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_ref_1992_; lean_object* v___x_1993_; lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2038_; 
v_ref_1992_ = lean_ctor_get(v___y_1989_, 5);
v___x_1993_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2038_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2038_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v_traceState_1999_; lean_object* v_env_2000_; lean_object* v_nextMacroScope_2001_; lean_object* v_ngen_2002_; lean_object* v_auxDeclNGen_2003_; lean_object* v_cache_2004_; lean_object* v_messages_2005_; lean_object* v_infoState_2006_; lean_object* v_snapshotTasks_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2037_; 
v___x_1998_ = lean_st_ref_take(v___y_1990_);
v_traceState_1999_ = lean_ctor_get(v___x_1998_, 4);
v_env_2000_ = lean_ctor_get(v___x_1998_, 0);
v_nextMacroScope_2001_ = lean_ctor_get(v___x_1998_, 1);
v_ngen_2002_ = lean_ctor_get(v___x_1998_, 2);
v_auxDeclNGen_2003_ = lean_ctor_get(v___x_1998_, 3);
v_cache_2004_ = lean_ctor_get(v___x_1998_, 5);
v_messages_2005_ = lean_ctor_get(v___x_1998_, 6);
v_infoState_2006_ = lean_ctor_get(v___x_1998_, 7);
v_snapshotTasks_2007_ = lean_ctor_get(v___x_1998_, 8);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2009_ = v___x_1998_;
v_isShared_2010_ = v_isSharedCheck_2037_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snapshotTasks_2007_);
lean_inc(v_infoState_2006_);
lean_inc(v_messages_2005_);
lean_inc(v_cache_2004_);
lean_inc(v_traceState_1999_);
lean_inc(v_auxDeclNGen_2003_);
lean_inc(v_ngen_2002_);
lean_inc(v_nextMacroScope_2001_);
lean_inc(v_env_2000_);
lean_dec(v___x_1998_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2037_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
uint64_t v_tid_2011_; lean_object* v_traces_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2036_; 
v_tid_2011_ = lean_ctor_get_uint64(v_traceState_1999_, sizeof(void*)*1);
v_traces_2012_ = lean_ctor_get(v_traceState_1999_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_traceState_1999_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2014_ = v_traceState_1999_;
v_isShared_2015_ = v_isSharedCheck_2036_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_traces_2012_);
lean_dec(v_traceState_1999_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2036_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; double v___x_2017_; uint8_t v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_2018_ = 0;
v___x_2019_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_2020_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2020_, 0, v_cls_1985_);
lean_ctor_set(v___x_2020_, 1, v___x_2016_);
lean_ctor_set(v___x_2020_, 2, v___x_2019_);
lean_ctor_set_float(v___x_2020_, sizeof(void*)*3, v___x_2017_);
lean_ctor_set_float(v___x_2020_, sizeof(void*)*3 + 8, v___x_2017_);
lean_ctor_set_uint8(v___x_2020_, sizeof(void*)*3 + 16, v___x_2018_);
v___x_2021_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_2022_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2020_);
lean_ctor_set(v___x_2022_, 1, v_a_1994_);
lean_ctor_set(v___x_2022_, 2, v___x_2021_);
lean_inc(v_ref_1992_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v_ref_1992_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = l_Lean_PersistentArray_push___redArg(v_traces_2012_, v___x_2023_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2024_);
v___x_2026_ = v___x_2014_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2024_);
lean_ctor_set_uint64(v_reuseFailAlloc_2035_, sizeof(void*)*1, v_tid_2011_);
v___x_2026_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2028_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v___x_2026_);
v___x_2028_ = v___x_2009_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_env_2000_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_nextMacroScope_2001_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_ngen_2002_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_auxDeclNGen_2003_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2034_, 5, v_cache_2004_);
lean_ctor_set(v_reuseFailAlloc_2034_, 6, v_messages_2005_);
lean_ctor_set(v_reuseFailAlloc_2034_, 7, v_infoState_2006_);
lean_ctor_set(v_reuseFailAlloc_2034_, 8, v_snapshotTasks_2007_);
v___x_2028_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2029_ = lean_st_ref_set(v___y_1990_, v___x_2028_);
v___x_2030_ = lean_box(0);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2030_);
v___x_2032_ = v___x_1996_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2039_, lean_object* v_msg_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2039_, v_msg_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2047_, lean_object* v_as_2048_, size_t v_sz_2049_, size_t v_i_2050_, lean_object* v_b_2051_){
_start:
{
lean_object* v_a_2054_; uint8_t v___x_2058_; 
v___x_2058_ = lean_usize_dec_lt(v_i_2050_, v_sz_2049_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_b_2051_);
return v___x_2059_;
}
else
{
lean_object* v_a_2060_; lean_object* v_defValue_2061_; uint8_t v___x_2062_; uint8_t v___y_2064_; 
v_a_2060_ = lean_array_uget(v_as_2048_, v_i_2050_);
v_defValue_2061_ = lean_ctor_get(v_a_2060_, 1);
v___x_2062_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2047_, v_a_2060_);
if (v___x_2062_ == 0)
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_unbox(v_defValue_2061_);
if (v___x_2076_ == 0)
{
v___y_2064_ = v___x_2058_;
goto v___jp_2063_;
}
else
{
v___y_2064_ = v___x_2062_;
goto v___jp_2063_;
}
}
else
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_unbox(v_defValue_2061_);
v___y_2064_ = v___x_2077_;
goto v___jp_2063_;
}
v___jp_2063_:
{
if (v___y_2064_ == 0)
{
lean_object* v_name_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2074_; 
v_name_2065_ = lean_ctor_get(v_a_2060_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_a_2060_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v_a_2060_, 1);
lean_dec(v_unused_2075_);
v___x_2067_ = v_a_2060_;
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_name_2065_);
lean_dec(v_a_2060_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2069_, 0, v___x_2062_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2069_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_name_2065_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_array_push(v_b_2051_, v___x_2071_);
v_a_2054_ = v___x_2072_;
goto v___jp_2053_;
}
}
}
else
{
lean_dec(v_a_2060_);
v_a_2054_ = v_b_2051_;
goto v___jp_2053_;
}
}
}
v___jp_2053_:
{
size_t v___x_2055_; size_t v___x_2056_; 
v___x_2055_ = ((size_t)1ULL);
v___x_2056_ = lean_usize_add(v_i_2050_, v___x_2055_);
v_i_2050_ = v___x_2056_;
v_b_2051_ = v_a_2054_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2078_, lean_object* v_as_2079_, lean_object* v_sz_2080_, lean_object* v_i_2081_, lean_object* v_b_2082_, lean_object* v___y_2083_){
_start:
{
size_t v_sz_boxed_2084_; size_t v_i_boxed_2085_; lean_object* v_res_2086_; 
v_sz_boxed_2084_ = lean_unbox_usize(v_sz_2080_);
lean_dec(v_sz_2080_);
v_i_boxed_2085_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2078_, v_as_2079_, v_sz_boxed_2084_, v_i_boxed_2085_, v_b_2082_);
lean_dec_ref(v_as_2079_);
lean_dec_ref(v___x_2078_);
return v_res_2086_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2089_; size_t v_sz_2090_; 
v___x_2089_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2090_ = lean_array_size(v___x_2089_);
return v_sz_2090_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2092_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
lean_ctor_set(v___x_2092_, 3, v___x_2091_);
lean_ctor_set(v___x_2092_, 4, v___x_2091_);
lean_ctor_set(v___x_2092_, 5, v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2101_ = l_Lean_Name_append(v___x_2100_, v___x_2099_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_options_2111_; lean_object* v_inheritedTraceOptions_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; size_t v_sz_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v_options_2111_ = lean_ctor_get(v_a_2108_, 2);
v_inheritedTraceOptions_2112_ = lean_ctor_get(v_a_2108_, 13);
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2115_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2116_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2111_, v___x_2115_, v_sz_2116_, v___x_2117_, v___x_2114_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2178_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2178_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2178_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_array_get_size(v_a_2119_);
v___x_2167_ = lean_nat_dec_eq(v___x_2166_, v___x_2113_);
if (v___x_2167_ == 0)
{
uint8_t v_hasTrace_2168_; 
v_hasTrace_2168_ = lean_ctor_get_uint8(v_options_2111_, sizeof(void*)*1);
if (v_hasTrace_2168_ == 0)
{
v___y_2124_ = v_a_2107_;
v___y_2125_ = v_a_2109_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2169_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2170_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2171_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2112_, v_options_2111_, v___x_2170_);
if (v___x_2171_ == 0)
{
v___y_2124_ = v_a_2107_;
v___y_2125_ = v_a_2109_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2172_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2105_);
v___x_2173_ = l_Lean_MessageData_ofName(v_declName_2105_);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2169_, v___x_2174_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_dec_ref_known(v___x_2175_, 1);
v___y_2124_ = v_a_2107_;
v___y_2125_ = v_a_2109_;
goto v___jp_2123_;
}
else
{
lean_del_object(v___x_2121_);
lean_dec(v_a_2119_);
lean_dec(v_declName_2105_);
return v___x_2175_;
}
}
}
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_del_object(v___x_2121_);
lean_dec(v_a_2119_);
lean_dec(v_declName_2105_);
v___x_2176_ = lean_box(0);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
v___jp_2123_:
{
lean_object* v___x_2126_; lean_object* v_env_2127_; lean_object* v_nextMacroScope_2128_; lean_object* v_ngen_2129_; lean_object* v_auxDeclNGen_2130_; lean_object* v_traceState_2131_; lean_object* v_messages_2132_; lean_object* v_infoState_2133_; lean_object* v_snapshotTasks_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2164_; 
v___x_2126_ = lean_st_ref_take(v___y_2125_);
v_env_2127_ = lean_ctor_get(v___x_2126_, 0);
v_nextMacroScope_2128_ = lean_ctor_get(v___x_2126_, 1);
v_ngen_2129_ = lean_ctor_get(v___x_2126_, 2);
v_auxDeclNGen_2130_ = lean_ctor_get(v___x_2126_, 3);
v_traceState_2131_ = lean_ctor_get(v___x_2126_, 4);
v_messages_2132_ = lean_ctor_get(v___x_2126_, 6);
v_infoState_2133_ = lean_ctor_get(v___x_2126_, 7);
v_snapshotTasks_2134_ = lean_ctor_get(v___x_2126_, 8);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v___x_2126_, 5);
lean_dec(v_unused_2165_);
v___x_2136_ = v___x_2126_;
v_isShared_2137_ = v_isSharedCheck_2164_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snapshotTasks_2134_);
lean_inc(v_infoState_2133_);
lean_inc(v_messages_2132_);
lean_inc(v_traceState_2131_);
lean_inc(v_auxDeclNGen_2130_);
lean_inc(v_ngen_2129_);
lean_inc(v_nextMacroScope_2128_);
lean_inc(v_env_2127_);
lean_dec(v___x_2126_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2164_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2138_ = l_Lean_Meta_eqnOptionsExt;
v___x_2139_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2138_, v_env_2127_, v_declName_2105_, v_a_2119_);
v___x_2140_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 5, v___x_2140_);
lean_ctor_set(v___x_2136_, 0, v___x_2139_);
v___x_2142_ = v___x_2136_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_nextMacroScope_2128_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_ngen_2129_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_auxDeclNGen_2130_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_traceState_2131_);
lean_ctor_set(v_reuseFailAlloc_2163_, 5, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2163_, 6, v_messages_2132_);
lean_ctor_set(v_reuseFailAlloc_2163_, 7, v_infoState_2133_);
lean_ctor_set(v_reuseFailAlloc_2163_, 8, v_snapshotTasks_2134_);
v___x_2142_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_mctx_2145_; lean_object* v_zetaDeltaFVarIds_2146_; lean_object* v_postponed_2147_; lean_object* v_diag_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2161_; 
v___x_2143_ = lean_st_ref_set(v___y_2125_, v___x_2142_);
v___x_2144_ = lean_st_ref_take(v___y_2124_);
v_mctx_2145_ = lean_ctor_get(v___x_2144_, 0);
v_zetaDeltaFVarIds_2146_ = lean_ctor_get(v___x_2144_, 2);
v_postponed_2147_ = lean_ctor_get(v___x_2144_, 3);
v_diag_2148_ = lean_ctor_get(v___x_2144_, 4);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v___x_2144_, 1);
lean_dec(v_unused_2162_);
v___x_2150_ = v___x_2144_;
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_diag_2148_);
lean_inc(v_postponed_2147_);
lean_inc(v_zetaDeltaFVarIds_2146_);
lean_inc(v_mctx_2145_);
lean_dec(v___x_2144_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v___x_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_mctx_2145_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_zetaDeltaFVarIds_2146_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_postponed_2147_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_diag_2148_);
v___x_2154_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2155_ = lean_st_ref_set(v___y_2124_, v___x_2154_);
v___x_2156_ = lean_box(0);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2156_);
v___x_2158_ = v___x_2121_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
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
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_declName_2105_);
v_a_2179_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2118_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2118_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2194_, lean_object* v_as_2195_, size_t v_sz_2196_, size_t v_i_2197_, lean_object* v_b_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2194_, v_as_2195_, v_sz_2196_, v_i_2197_, v_b_2198_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2205_, lean_object* v_as_2206_, lean_object* v_sz_2207_, lean_object* v_i_2208_, lean_object* v_b_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
size_t v_sz_boxed_2215_; size_t v_i_boxed_2216_; lean_object* v_res_2217_; 
v_sz_boxed_2215_ = lean_unbox_usize(v_sz_2207_);
lean_dec(v_sz_2207_);
v_i_boxed_2216_ = lean_unbox_usize(v_i_2208_);
lean_dec(v_i_2208_);
v_res_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2205_, v_as_2206_, v_sz_boxed_2215_, v_i_boxed_2216_, v_b_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec_ref(v_as_2206_);
lean_dec_ref(v___x_2205_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_st_mk_ref(v___x_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2243_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2243_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2243_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
uint8_t v___x_2231_; 
v___x_2231_ = lean_unbox(v_a_2227_);
lean_dec(v_a_2227_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_dec_ref(v_f_2224_);
v___x_2232_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 1);
lean_ctor_set(v___x_2229_, 0, v___x_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2236_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2237_ = lean_st_ref_take(v___x_2236_);
v___x_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_f_2224_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_st_ref_set(v___x_2236_, v___x_2238_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2239_);
v___x_2241_ = v___x_2229_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v_f_2224_);
v_a_2244_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2226_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2226_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2258_, lean_object* v_as_x27_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
if (lean_obj_tag(v_as_x27_2259_) == 0)
{
lean_object* v___x_2266_; 
lean_dec(v_declName_2258_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_b_2260_);
return v___x_2266_;
}
else
{
lean_object* v_head_2267_; lean_object* v_tail_2268_; lean_object* v___x_2269_; 
lean_dec_ref(v_b_2260_);
v_head_2267_ = lean_ctor_get(v_as_x27_2259_, 0);
v_tail_2268_ = lean_ctor_get(v_as_x27_2259_, 1);
lean_inc(v_head_2267_);
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc(v_declName_2258_);
v___x_2269_ = lean_apply_6(v_head_2267_, v_declName_2258_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, lean_box(0));
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2282_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2282_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2282_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_box(0);
if (lean_obj_tag(v_a_2270_) == 1)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
lean_dec(v_declName_2258_);
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_a_2270_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v___x_2274_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2276_);
v___x_2278_ = v___x_2272_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
else
{
lean_object* v___x_2280_; 
lean_del_object(v___x_2272_);
lean_dec(v_a_2270_);
v___x_2280_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2259_ = v_tail_2268_;
v_b_2260_ = v___x_2280_;
goto _start;
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_declName_2258_);
v_a_2283_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2269_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2269_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2291_, lean_object* v_as_x27_2292_, lean_object* v_b_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2291_, v_as_x27_2292_, v_b_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v_as_x27_2292_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2300_, lean_object* v_declName_2301_, uint8_t v_nonRec_2302_, lean_object* v___x_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2312_; lean_object* v_env_2313_; uint8_t v___x_2314_; uint8_t v___x_2315_; 
v___x_2312_ = lean_st_ref_get(v___y_2307_);
v_env_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc_ref(v_env_2313_);
lean_dec(v___x_2312_);
v___x_2314_ = 1;
lean_inc(v___x_2300_);
v___x_2315_ = l_Lean_Environment_contains(v_env_2313_, v___x_2300_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; 
lean_dec(v___x_2300_);
lean_inc(v_declName_2301_);
v___x_2316_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2301_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; uint8_t v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = lean_unbox(v_a_2317_);
lean_dec(v_a_2317_);
if (v___x_2318_ == 0)
{
lean_dec_ref(v___x_2303_);
lean_dec(v_declName_2301_);
goto v___jp_2309_;
}
else
{
lean_object* v___x_2319_; 
lean_inc(v_declName_2301_);
v___x_2319_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2301_, v___y_2307_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; uint8_t v___x_2321_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2321_ = lean_unbox(v_a_2320_);
lean_dec(v_a_2320_);
if (v___x_2321_ == 0)
{
if (v_nonRec_2302_ == 0)
{
lean_dec_ref(v___x_2303_);
lean_dec(v_declName_2301_);
goto v___jp_2309_;
}
else
{
lean_object* v___x_2322_; lean_object* v_env_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2322_ = lean_st_ref_get(v___y_2307_);
v_env_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc_ref(v_env_2323_);
lean_dec(v___x_2322_);
lean_inc(v_declName_2301_);
v___x_2324_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2323_, v_declName_2301_, v___x_2303_);
v___x_2325_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2301_, v___x_2324_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
return v___x_2325_;
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec_ref(v___x_2303_);
v___x_2326_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2327_ = lean_st_ref_get(v___x_2326_);
v___x_2328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2329_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2301_, v___x_2327_, v___x_2328_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___x_2327_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2339_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2339_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2339_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v_fst_2334_; 
v_fst_2334_ = lean_ctor_get(v_a_2330_, 0);
lean_inc(v_fst_2334_);
lean_dec(v_a_2330_);
if (lean_obj_tag(v_fst_2334_) == 0)
{
lean_del_object(v___x_2332_);
goto v___jp_2309_;
}
else
{
lean_object* v_val_2335_; lean_object* v___x_2337_; 
v_val_2335_ = lean_ctor_get(v_fst_2334_, 0);
lean_inc(v_val_2335_);
lean_dec_ref_known(v_fst_2334_, 1);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v_val_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_val_2335_);
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
v_a_2340_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2329_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2329_);
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
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v___x_2303_);
lean_dec(v_declName_2301_);
v_a_2348_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2319_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2319_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v___x_2303_);
lean_dec(v_declName_2301_);
v_a_2356_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2316_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2316_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec_ref(v___x_2303_);
lean_dec(v_declName_2301_);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2300_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
v___jp_2309_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2366_, lean_object* v_declName_2367_, lean_object* v_nonRec_2368_, lean_object* v___x_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
uint8_t v_nonRec_boxed_2375_; lean_object* v_res_2376_; 
v_nonRec_boxed_2375_ = lean_unbox(v_nonRec_2368_);
v_res_2376_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2366_, v_declName_2367_, v_nonRec_boxed_2375_, v___x_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_ref_2383_; lean_object* v___x_2384_; lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
v_ref_2383_ = lean_ctor_get(v___y_2380_, 5);
v___x_2384_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
lean_inc(v_ref_2383_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_ref_2383_);
lean_ctor_set(v___x_2389_, 1, v_a_2385_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 1);
lean_ctor_set(v___x_2387_, 0, v___x_2389_);
v___x_2391_ = v___x_2387_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2401_, uint8_t v_isExporting_2402_, lean_object* v___x_2403_, lean_object* v___y_2404_, lean_object* v___x_2405_, lean_object* v_a_x3f_2406_){
_start:
{
lean_object* v___x_2408_; lean_object* v_env_2409_; lean_object* v_nextMacroScope_2410_; lean_object* v_ngen_2411_; lean_object* v_auxDeclNGen_2412_; lean_object* v_traceState_2413_; lean_object* v_messages_2414_; lean_object* v_infoState_2415_; lean_object* v_snapshotTasks_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2441_; 
v___x_2408_ = lean_st_ref_take(v___y_2401_);
v_env_2409_ = lean_ctor_get(v___x_2408_, 0);
v_nextMacroScope_2410_ = lean_ctor_get(v___x_2408_, 1);
v_ngen_2411_ = lean_ctor_get(v___x_2408_, 2);
v_auxDeclNGen_2412_ = lean_ctor_get(v___x_2408_, 3);
v_traceState_2413_ = lean_ctor_get(v___x_2408_, 4);
v_messages_2414_ = lean_ctor_get(v___x_2408_, 6);
v_infoState_2415_ = lean_ctor_get(v___x_2408_, 7);
v_snapshotTasks_2416_ = lean_ctor_get(v___x_2408_, 8);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v___x_2408_, 5);
lean_dec(v_unused_2442_);
v___x_2418_ = v___x_2408_;
v_isShared_2419_ = v_isSharedCheck_2441_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_snapshotTasks_2416_);
lean_inc(v_infoState_2415_);
lean_inc(v_messages_2414_);
lean_inc(v_traceState_2413_);
lean_inc(v_auxDeclNGen_2412_);
lean_inc(v_ngen_2411_);
lean_inc(v_nextMacroScope_2410_);
lean_inc(v_env_2409_);
lean_dec(v___x_2408_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2441_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = l_Lean_Environment_setExporting(v_env_2409_, v_isExporting_2402_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 5, v___x_2403_);
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_nextMacroScope_2410_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_ngen_2411_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_auxDeclNGen_2412_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_traceState_2413_);
lean_ctor_set(v_reuseFailAlloc_2440_, 5, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2440_, 6, v_messages_2414_);
lean_ctor_set(v_reuseFailAlloc_2440_, 7, v_infoState_2415_);
lean_ctor_set(v_reuseFailAlloc_2440_, 8, v_snapshotTasks_2416_);
v___x_2422_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_mctx_2425_; lean_object* v_zetaDeltaFVarIds_2426_; lean_object* v_postponed_2427_; lean_object* v_diag_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2438_; 
v___x_2423_ = lean_st_ref_set(v___y_2401_, v___x_2422_);
v___x_2424_ = lean_st_ref_take(v___y_2404_);
v_mctx_2425_ = lean_ctor_get(v___x_2424_, 0);
v_zetaDeltaFVarIds_2426_ = lean_ctor_get(v___x_2424_, 2);
v_postponed_2427_ = lean_ctor_get(v___x_2424_, 3);
v_diag_2428_ = lean_ctor_get(v___x_2424_, 4);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; 
v_unused_2439_ = lean_ctor_get(v___x_2424_, 1);
lean_dec(v_unused_2439_);
v___x_2430_ = v___x_2424_;
v_isShared_2431_ = v_isSharedCheck_2438_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_diag_2428_);
lean_inc(v_postponed_2427_);
lean_inc(v_zetaDeltaFVarIds_2426_);
lean_inc(v_mctx_2425_);
lean_dec(v___x_2424_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2438_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v___x_2405_);
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_mctx_2425_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_zetaDeltaFVarIds_2426_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_postponed_2427_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_diag_2428_);
v___x_2433_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_st_ref_set(v___y_2404_, v___x_2433_);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2443_, lean_object* v_isExporting_2444_, lean_object* v___x_2445_, lean_object* v___y_2446_, lean_object* v___x_2447_, lean_object* v_a_x3f_2448_, lean_object* v___y_2449_){
_start:
{
uint8_t v_isExporting_boxed_2450_; lean_object* v_res_2451_; 
v_isExporting_boxed_2450_ = lean_unbox(v_isExporting_2444_);
v_res_2451_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2443_, v_isExporting_boxed_2450_, v___x_2445_, v___y_2446_, v___x_2447_, v_a_x3f_2448_);
lean_dec(v_a_x3f_2448_);
lean_dec(v___y_2446_);
lean_dec(v___y_2443_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2452_, uint8_t v_isExporting_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; lean_object* v_env_2460_; uint8_t v_isExporting_2461_; lean_object* v___x_2462_; lean_object* v_env_2463_; lean_object* v_nextMacroScope_2464_; lean_object* v_ngen_2465_; lean_object* v_auxDeclNGen_2466_; lean_object* v_traceState_2467_; lean_object* v_messages_2468_; lean_object* v_infoState_2469_; lean_object* v_snapshotTasks_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2524_; 
v___x_2459_ = lean_st_ref_get(v___y_2457_);
v_env_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc_ref(v_env_2460_);
lean_dec(v___x_2459_);
v_isExporting_2461_ = lean_ctor_get_uint8(v_env_2460_, sizeof(void*)*8);
lean_dec_ref(v_env_2460_);
v___x_2462_ = lean_st_ref_take(v___y_2457_);
v_env_2463_ = lean_ctor_get(v___x_2462_, 0);
v_nextMacroScope_2464_ = lean_ctor_get(v___x_2462_, 1);
v_ngen_2465_ = lean_ctor_get(v___x_2462_, 2);
v_auxDeclNGen_2466_ = lean_ctor_get(v___x_2462_, 3);
v_traceState_2467_ = lean_ctor_get(v___x_2462_, 4);
v_messages_2468_ = lean_ctor_get(v___x_2462_, 6);
v_infoState_2469_ = lean_ctor_get(v___x_2462_, 7);
v_snapshotTasks_2470_ = lean_ctor_get(v___x_2462_, 8);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; 
v_unused_2525_ = lean_ctor_get(v___x_2462_, 5);
lean_dec(v_unused_2525_);
v___x_2472_ = v___x_2462_;
v_isShared_2473_ = v_isSharedCheck_2524_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_snapshotTasks_2470_);
lean_inc(v_infoState_2469_);
lean_inc(v_messages_2468_);
lean_inc(v_traceState_2467_);
lean_inc(v_auxDeclNGen_2466_);
lean_inc(v_ngen_2465_);
lean_inc(v_nextMacroScope_2464_);
lean_inc(v_env_2463_);
lean_dec(v___x_2462_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2524_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2474_ = l_Lean_Environment_setExporting(v_env_2463_, v_isExporting_2453_);
v___x_2475_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 5, v___x_2475_);
lean_ctor_set(v___x_2472_, 0, v___x_2474_);
v___x_2477_ = v___x_2472_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_nextMacroScope_2464_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_ngen_2465_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_auxDeclNGen_2466_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_traceState_2467_);
lean_ctor_set(v_reuseFailAlloc_2523_, 5, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2523_, 6, v_messages_2468_);
lean_ctor_set(v_reuseFailAlloc_2523_, 7, v_infoState_2469_);
lean_ctor_set(v_reuseFailAlloc_2523_, 8, v_snapshotTasks_2470_);
v___x_2477_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_mctx_2480_; lean_object* v_zetaDeltaFVarIds_2481_; lean_object* v_postponed_2482_; lean_object* v_diag_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2521_; 
v___x_2478_ = lean_st_ref_set(v___y_2457_, v___x_2477_);
v___x_2479_ = lean_st_ref_take(v___y_2455_);
v_mctx_2480_ = lean_ctor_get(v___x_2479_, 0);
v_zetaDeltaFVarIds_2481_ = lean_ctor_get(v___x_2479_, 2);
v_postponed_2482_ = lean_ctor_get(v___x_2479_, 3);
v_diag_2483_ = lean_ctor_get(v___x_2479_, 4);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; 
v_unused_2522_ = lean_ctor_get(v___x_2479_, 1);
lean_dec(v_unused_2522_);
v___x_2485_ = v___x_2479_;
v_isShared_2486_ = v_isSharedCheck_2521_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_diag_2483_);
lean_inc(v_postponed_2482_);
lean_inc(v_zetaDeltaFVarIds_2481_);
lean_inc(v_mctx_2480_);
lean_dec(v___x_2479_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2521_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2487_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2487_);
v___x_2489_ = v___x_2485_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_mctx_2480_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_zetaDeltaFVarIds_2481_);
lean_ctor_set(v_reuseFailAlloc_2520_, 3, v_postponed_2482_);
lean_ctor_set(v_reuseFailAlloc_2520_, 4, v_diag_2483_);
v___x_2489_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2490_; lean_object* v_r_2491_; 
v___x_2490_ = lean_st_ref_set(v___y_2455_, v___x_2489_);
lean_inc(v___y_2457_);
lean_inc_ref(v___y_2456_);
lean_inc(v___y_2455_);
lean_inc_ref(v___y_2454_);
v_r_2491_ = lean_apply_5(v_x_2452_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, lean_box(0));
if (lean_obj_tag(v_r_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2508_; 
v_a_2492_ = lean_ctor_get(v_r_2491_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_r_2491_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2494_ = v_r_2491_;
v_isShared_2495_ = v_isSharedCheck_2508_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v_r_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2508_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
lean_inc(v_a_2492_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 1);
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v___x_2498_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2457_, v_isExporting_2461_, v___x_2475_, v___y_2455_, v___x_2487_, v___x_2497_);
lean_dec_ref(v___x_2497_);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v___x_2498_, 0);
lean_dec(v_unused_2506_);
v___x_2500_ = v___x_2498_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_dec(v___x_2498_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v_a_2492_);
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2492_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
v_a_2509_ = lean_ctor_get(v_r_2491_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v_r_2491_, 1);
v___x_2510_ = lean_box(0);
v___x_2511_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2457_, v_isExporting_2461_, v___x_2475_, v___y_2455_, v___x_2487_, v___x_2510_);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v___x_2511_, 0);
lean_dec(v_unused_2519_);
v___x_2513_ = v___x_2511_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_dec(v___x_2511_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set_tag(v___x_2513_, 1);
lean_ctor_set(v___x_2513_, 0, v_a_2509_);
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2509_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2526_, lean_object* v_isExporting_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
uint8_t v_isExporting_boxed_2533_; lean_object* v_res_2534_; 
v_isExporting_boxed_2533_ = lean_unbox(v_isExporting_2527_);
v_res_2534_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2526_, v_isExporting_boxed_2533_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2535_, uint8_t v_when_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
if (v_when_2536_ == 0)
{
lean_object* v___x_2542_; 
lean_inc(v___y_2540_);
lean_inc_ref(v___y_2539_);
lean_inc(v___y_2538_);
lean_inc_ref(v___y_2537_);
v___x_2542_ = lean_apply_5(v_x_2535_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, lean_box(0));
return v___x_2542_;
}
else
{
uint8_t v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = 0;
v___x_2544_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2535_, v___x_2543_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2545_, lean_object* v_when_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
uint8_t v_when_boxed_2552_; lean_object* v_res_2553_; 
v_when_boxed_2552_ = lean_unbox(v_when_2546_);
v_res_2553_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2545_, v_when_boxed_2552_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2553_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2556_ = l_Lean_stringToMessageData(v___x_2555_);
return v___x_2556_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2559_ = l_Lean_stringToMessageData(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2562_ = l_Lean_stringToMessageData(v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2563_, uint8_t v_nonRec_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v_env_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___f_2575_; uint8_t v___x_2576_; lean_object* v___x_2577_; 
v___x_2570_ = lean_st_ref_get(v___y_2568_);
v_env_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_ref(v_env_2571_);
lean_dec(v___x_2570_);
v___x_2572_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2563_);
v___x_2573_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2571_, v_declName_2563_, v___x_2572_);
v___x_2574_ = lean_box(v_nonRec_2564_);
lean_inc(v___x_2573_);
v___f_2575_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2575_, 0, v___x_2573_);
lean_closure_set(v___f_2575_, 1, v_declName_2563_);
lean_closure_set(v___f_2575_, 2, v___x_2574_);
lean_closure_set(v___f_2575_, 3, v___x_2572_);
v___x_2576_ = 1;
v___x_2577_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2575_, v___x_2576_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
if (lean_obj_tag(v_a_2578_) == 1)
{
lean_object* v_val_2579_; uint8_t v___x_2580_; 
v_val_2579_ = lean_ctor_get(v_a_2578_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v_a_2578_, 1);
v___x_2580_ = lean_name_eq(v_val_2579_, v___x_2573_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref_known(v___x_2577_, 1);
v___x_2581_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2582_ = l_Lean_MessageData_ofName(v_val_2579_);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = l_Lean_MessageData_ofName(v___x_2573_);
v___x_2587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2589_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
lean_dec(v_val_2579_);
lean_dec(v___x_2573_);
return v___x_2577_;
}
}
else
{
lean_dec(v_a_2578_);
lean_dec(v___x_2573_);
return v___x_2577_;
}
}
else
{
lean_dec(v___x_2573_);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2599_, lean_object* v_nonRec_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
uint8_t v_nonRec_boxed_2606_; lean_object* v_res_2607_; 
v_nonRec_boxed_2606_ = lean_unbox(v_nonRec_2600_);
v_res_2607_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2599_, v_nonRec_boxed_2606_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2608_, uint8_t v_nonRec_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2615_ = lean_box(v_nonRec_2609_);
v___f_2616_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2616_, 0, v_declName_2608_);
lean_closure_set(v___f_2616_, 1, v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(32u);
v___x_2618_ = lean_mk_empty_array_with_capacity(v___x_2617_);
lean_dec_ref(v___x_2618_);
v___x_2619_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2620_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2621_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2619_, v___x_2620_, v___f_2616_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2622_, lean_object* v_nonRec_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
uint8_t v_nonRec_boxed_2629_; lean_object* v_res_2630_; 
v_nonRec_boxed_2629_ = lean_unbox(v_nonRec_2623_);
v_res_2630_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2622_, v_nonRec_boxed_2629_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2631_, lean_object* v_as_2632_, lean_object* v_as_x27_2633_, lean_object* v_b_2634_, lean_object* v_a_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2631_, v_as_x27_2633_, v_b_2634_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2642_, lean_object* v_as_2643_, lean_object* v_as_x27_2644_, lean_object* v_b_2645_, lean_object* v_a_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2642_, v_as_2643_, v_as_x27_2644_, v_b_2645_, v_a_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v_as_x27_2644_);
lean_dec(v_as_2643_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2653_, lean_object* v_x_2654_, uint8_t v_isExporting_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2654_, v_isExporting_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_x_2663_, lean_object* v_isExporting_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v_isExporting_boxed_2670_; lean_object* v_res_2671_; 
v_isExporting_boxed_2670_ = lean_unbox(v_isExporting_2664_);
v_res_2671_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2662_, v_x_2663_, v_isExporting_boxed_2670_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2672_, lean_object* v_x_2673_, uint8_t v_when_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2673_, v_when_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2681_, lean_object* v_x_2682_, lean_object* v_when_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v_when_boxed_2689_; lean_object* v_res_2690_; 
v_when_boxed_2689_ = lean_unbox(v_when_2683_);
v_res_2690_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2681_, v_x_2682_, v_when_boxed_2689_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2691_, lean_object* v_msg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2699_, lean_object* v_msg_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2699_, v_msg_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v_res_2706_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_unsigned_to_nat(32u);
v___x_2708_ = lean_mk_empty_array_with_capacity(v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2710_ = ((size_t)5ULL);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_unsigned_to_nat(32u);
v___x_2713_ = lean_mk_empty_array_with_capacity(v___x_2712_);
v___x_2714_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2715_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v___x_2713_);
lean_ctor_set(v___x_2715_, 2, v___x_2711_);
lean_ctor_set(v___x_2715_, 3, v___x_2711_);
lean_ctor_set_usize(v___x_2715_, 4, v___x_2710_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; lean_object* v_traceState_2719_; lean_object* v_traces_2720_; lean_object* v___x_2721_; lean_object* v_traceState_2722_; lean_object* v_env_2723_; lean_object* v_nextMacroScope_2724_; lean_object* v_ngen_2725_; lean_object* v_auxDeclNGen_2726_; lean_object* v_cache_2727_; lean_object* v_messages_2728_; lean_object* v_infoState_2729_; lean_object* v_snapshotTasks_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2749_; 
v___x_2718_ = lean_st_ref_get(v___y_2716_);
v_traceState_2719_ = lean_ctor_get(v___x_2718_, 4);
lean_inc_ref(v_traceState_2719_);
lean_dec(v___x_2718_);
v_traces_2720_ = lean_ctor_get(v_traceState_2719_, 0);
lean_inc_ref(v_traces_2720_);
lean_dec_ref(v_traceState_2719_);
v___x_2721_ = lean_st_ref_take(v___y_2716_);
v_traceState_2722_ = lean_ctor_get(v___x_2721_, 4);
v_env_2723_ = lean_ctor_get(v___x_2721_, 0);
v_nextMacroScope_2724_ = lean_ctor_get(v___x_2721_, 1);
v_ngen_2725_ = lean_ctor_get(v___x_2721_, 2);
v_auxDeclNGen_2726_ = lean_ctor_get(v___x_2721_, 3);
v_cache_2727_ = lean_ctor_get(v___x_2721_, 5);
v_messages_2728_ = lean_ctor_get(v___x_2721_, 6);
v_infoState_2729_ = lean_ctor_get(v___x_2721_, 7);
v_snapshotTasks_2730_ = lean_ctor_get(v___x_2721_, 8);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2732_ = v___x_2721_;
v_isShared_2733_ = v_isSharedCheck_2749_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_snapshotTasks_2730_);
lean_inc(v_infoState_2729_);
lean_inc(v_messages_2728_);
lean_inc(v_cache_2727_);
lean_inc(v_traceState_2722_);
lean_inc(v_auxDeclNGen_2726_);
lean_inc(v_ngen_2725_);
lean_inc(v_nextMacroScope_2724_);
lean_inc(v_env_2723_);
lean_dec(v___x_2721_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2749_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
uint64_t v_tid_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2747_; 
v_tid_2734_ = lean_ctor_get_uint64(v_traceState_2722_, sizeof(void*)*1);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_traceState_2722_);
if (v_isSharedCheck_2747_ == 0)
{
lean_object* v_unused_2748_; 
v_unused_2748_ = lean_ctor_get(v_traceState_2722_, 0);
lean_dec(v_unused_2748_);
v___x_2736_ = v_traceState_2722_;
v_isShared_2737_ = v_isSharedCheck_2747_;
goto v_resetjp_2735_;
}
else
{
lean_dec(v_traceState_2722_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2747_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2738_);
v___x_2740_ = v___x_2736_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2738_);
lean_ctor_set_uint64(v_reuseFailAlloc_2746_, sizeof(void*)*1, v_tid_2734_);
v___x_2740_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2742_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 4, v___x_2740_);
v___x_2742_ = v___x_2732_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_env_2723_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_nextMacroScope_2724_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_ngen_2725_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_auxDeclNGen_2726_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2745_, 5, v_cache_2727_);
lean_ctor_set(v_reuseFailAlloc_2745_, 6, v_messages_2728_);
lean_ctor_set(v_reuseFailAlloc_2745_, 7, v_infoState_2729_);
lean_ctor_set(v_reuseFailAlloc_2745_, 8, v_snapshotTasks_2730_);
v___x_2742_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = lean_st_ref_set(v___y_2716_, v___x_2742_);
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v_traces_2720_);
return v___x_2744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2750_);
lean_dec(v___y_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2757_, v___y_2758_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = 0;
v___x_2766_ = lean_box(v___x_2765_);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2775_ = l_Lean_stringToMessageData(v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2776_, lean_object* v_x_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2781_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2782_ = l_Lean_MessageData_ofName(v_name_2776_);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2785_, lean_object* v_x_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2785_, v_x_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec_ref(v_x_2786_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2791_){
_start:
{
if (lean_obj_tag(v_x_2791_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v_x_2791_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_x_2791_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v_x_2791_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v_x_2791_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set_tag(v___x_2795_, 1);
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_a_2801_ = lean_ctor_get(v_x_2791_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_x_2791_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v_x_2791_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v_x_2791_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set_tag(v___x_2803_, 0);
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2809_);
return v_res_2811_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2812_){
_start:
{
if (lean_obj_tag(v_e_2812_) == 0)
{
uint8_t v___x_2813_; 
v___x_2813_ = 2;
return v___x_2813_;
}
else
{
lean_object* v_a_2814_; uint8_t v___x_2815_; 
v_a_2814_ = lean_ctor_get(v_e_2812_, 0);
v___x_2815_ = lean_unbox(v_a_2814_);
if (v___x_2815_ == 0)
{
uint8_t v___x_2816_; 
v___x_2816_ = 1;
return v___x_2816_;
}
else
{
uint8_t v___x_2817_; 
v___x_2817_ = 0;
return v___x_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2818_){
_start:
{
uint8_t v_res_2819_; lean_object* v_r_2820_; 
v_res_2819_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2818_);
lean_dec_ref(v_e_2818_);
v_r_2820_ = lean_box(v_res_2819_);
return v_r_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2821_, size_t v_i_2822_, lean_object* v_bs_2823_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_usize_dec_lt(v_i_2822_, v_sz_2821_);
if (v___x_2824_ == 0)
{
return v_bs_2823_;
}
else
{
lean_object* v_v_2825_; lean_object* v_msg_2826_; lean_object* v___x_2827_; lean_object* v_bs_x27_2828_; size_t v___x_2829_; size_t v___x_2830_; lean_object* v___x_2831_; 
v_v_2825_ = lean_array_uget_borrowed(v_bs_2823_, v_i_2822_);
v_msg_2826_ = lean_ctor_get(v_v_2825_, 1);
lean_inc_ref(v_msg_2826_);
v___x_2827_ = lean_unsigned_to_nat(0u);
v_bs_x27_2828_ = lean_array_uset(v_bs_2823_, v_i_2822_, v___x_2827_);
v___x_2829_ = ((size_t)1ULL);
v___x_2830_ = lean_usize_add(v_i_2822_, v___x_2829_);
v___x_2831_ = lean_array_uset(v_bs_x27_2828_, v_i_2822_, v_msg_2826_);
v_i_2822_ = v___x_2830_;
v_bs_2823_ = v___x_2831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2833_, lean_object* v_i_2834_, lean_object* v_bs_2835_){
_start:
{
size_t v_sz_boxed_2836_; size_t v_i_boxed_2837_; lean_object* v_res_2838_; 
v_sz_boxed_2836_ = lean_unbox_usize(v_sz_2833_);
lean_dec(v_sz_2833_);
v_i_boxed_2837_ = lean_unbox_usize(v_i_2834_);
lean_dec(v_i_2834_);
v_res_2838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2836_, v_i_boxed_2837_, v_bs_2835_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2839_, lean_object* v_data_2840_, lean_object* v_ref_2841_, lean_object* v_msg_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_fileName_2846_; lean_object* v_fileMap_2847_; lean_object* v_options_2848_; lean_object* v_currRecDepth_2849_; lean_object* v_maxRecDepth_2850_; lean_object* v_ref_2851_; lean_object* v_currNamespace_2852_; lean_object* v_openDecls_2853_; lean_object* v_initHeartbeats_2854_; lean_object* v_maxHeartbeats_2855_; lean_object* v_quotContext_2856_; lean_object* v_currMacroScope_2857_; uint8_t v_diag_2858_; lean_object* v_cancelTk_x3f_2859_; uint8_t v_suppressElabErrors_2860_; lean_object* v_inheritedTraceOptions_2861_; lean_object* v___x_2862_; lean_object* v_traceState_2863_; lean_object* v_traces_2864_; lean_object* v_ref_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; size_t v_sz_2868_; size_t v___x_2869_; lean_object* v___x_2870_; lean_object* v_msg_2871_; lean_object* v___x_2872_; lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2910_; 
v_fileName_2846_ = lean_ctor_get(v___y_2843_, 0);
v_fileMap_2847_ = lean_ctor_get(v___y_2843_, 1);
v_options_2848_ = lean_ctor_get(v___y_2843_, 2);
v_currRecDepth_2849_ = lean_ctor_get(v___y_2843_, 3);
v_maxRecDepth_2850_ = lean_ctor_get(v___y_2843_, 4);
v_ref_2851_ = lean_ctor_get(v___y_2843_, 5);
v_currNamespace_2852_ = lean_ctor_get(v___y_2843_, 6);
v_openDecls_2853_ = lean_ctor_get(v___y_2843_, 7);
v_initHeartbeats_2854_ = lean_ctor_get(v___y_2843_, 8);
v_maxHeartbeats_2855_ = lean_ctor_get(v___y_2843_, 9);
v_quotContext_2856_ = lean_ctor_get(v___y_2843_, 10);
v_currMacroScope_2857_ = lean_ctor_get(v___y_2843_, 11);
v_diag_2858_ = lean_ctor_get_uint8(v___y_2843_, sizeof(void*)*14);
v_cancelTk_x3f_2859_ = lean_ctor_get(v___y_2843_, 12);
v_suppressElabErrors_2860_ = lean_ctor_get_uint8(v___y_2843_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2861_ = lean_ctor_get(v___y_2843_, 13);
v___x_2862_ = lean_st_ref_get(v___y_2844_);
v_traceState_2863_ = lean_ctor_get(v___x_2862_, 4);
lean_inc_ref(v_traceState_2863_);
lean_dec(v___x_2862_);
v_traces_2864_ = lean_ctor_get(v_traceState_2863_, 0);
lean_inc_ref(v_traces_2864_);
lean_dec_ref(v_traceState_2863_);
v_ref_2865_ = l_Lean_replaceRef(v_ref_2841_, v_ref_2851_);
lean_inc_ref(v_inheritedTraceOptions_2861_);
lean_inc(v_cancelTk_x3f_2859_);
lean_inc(v_currMacroScope_2857_);
lean_inc(v_quotContext_2856_);
lean_inc(v_maxHeartbeats_2855_);
lean_inc(v_initHeartbeats_2854_);
lean_inc(v_openDecls_2853_);
lean_inc(v_currNamespace_2852_);
lean_inc(v_maxRecDepth_2850_);
lean_inc(v_currRecDepth_2849_);
lean_inc_ref(v_options_2848_);
lean_inc_ref(v_fileMap_2847_);
lean_inc_ref(v_fileName_2846_);
v___x_2866_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2866_, 0, v_fileName_2846_);
lean_ctor_set(v___x_2866_, 1, v_fileMap_2847_);
lean_ctor_set(v___x_2866_, 2, v_options_2848_);
lean_ctor_set(v___x_2866_, 3, v_currRecDepth_2849_);
lean_ctor_set(v___x_2866_, 4, v_maxRecDepth_2850_);
lean_ctor_set(v___x_2866_, 5, v_ref_2865_);
lean_ctor_set(v___x_2866_, 6, v_currNamespace_2852_);
lean_ctor_set(v___x_2866_, 7, v_openDecls_2853_);
lean_ctor_set(v___x_2866_, 8, v_initHeartbeats_2854_);
lean_ctor_set(v___x_2866_, 9, v_maxHeartbeats_2855_);
lean_ctor_set(v___x_2866_, 10, v_quotContext_2856_);
lean_ctor_set(v___x_2866_, 11, v_currMacroScope_2857_);
lean_ctor_set(v___x_2866_, 12, v_cancelTk_x3f_2859_);
lean_ctor_set(v___x_2866_, 13, v_inheritedTraceOptions_2861_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*14, v_diag_2858_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*14 + 1, v_suppressElabErrors_2860_);
v___x_2867_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2864_);
lean_dec_ref(v_traces_2864_);
v_sz_2868_ = lean_array_size(v___x_2867_);
v___x_2869_ = ((size_t)0ULL);
v___x_2870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2868_, v___x_2869_, v___x_2867_);
v_msg_2871_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2871_, 0, v_data_2840_);
lean_ctor_set(v_msg_2871_, 1, v_msg_2842_);
lean_ctor_set(v_msg_2871_, 2, v___x_2870_);
v___x_2872_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2871_, v___x_2866_, v___y_2844_);
lean_dec_ref_known(v___x_2866_, 14);
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2910_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2910_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v_traceState_2878_; lean_object* v_env_2879_; lean_object* v_nextMacroScope_2880_; lean_object* v_ngen_2881_; lean_object* v_auxDeclNGen_2882_; lean_object* v_cache_2883_; lean_object* v_messages_2884_; lean_object* v_infoState_2885_; lean_object* v_snapshotTasks_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2909_; 
v___x_2877_ = lean_st_ref_take(v___y_2844_);
v_traceState_2878_ = lean_ctor_get(v___x_2877_, 4);
v_env_2879_ = lean_ctor_get(v___x_2877_, 0);
v_nextMacroScope_2880_ = lean_ctor_get(v___x_2877_, 1);
v_ngen_2881_ = lean_ctor_get(v___x_2877_, 2);
v_auxDeclNGen_2882_ = lean_ctor_get(v___x_2877_, 3);
v_cache_2883_ = lean_ctor_get(v___x_2877_, 5);
v_messages_2884_ = lean_ctor_get(v___x_2877_, 6);
v_infoState_2885_ = lean_ctor_get(v___x_2877_, 7);
v_snapshotTasks_2886_ = lean_ctor_get(v___x_2877_, 8);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2888_ = v___x_2877_;
v_isShared_2889_ = v_isSharedCheck_2909_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_snapshotTasks_2886_);
lean_inc(v_infoState_2885_);
lean_inc(v_messages_2884_);
lean_inc(v_cache_2883_);
lean_inc(v_traceState_2878_);
lean_inc(v_auxDeclNGen_2882_);
lean_inc(v_ngen_2881_);
lean_inc(v_nextMacroScope_2880_);
lean_inc(v_env_2879_);
lean_dec(v___x_2877_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2909_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
uint64_t v_tid_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2907_; 
v_tid_2890_ = lean_ctor_get_uint64(v_traceState_2878_, sizeof(void*)*1);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_traceState_2878_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v_traceState_2878_, 0);
lean_dec(v_unused_2908_);
v___x_2892_ = v_traceState_2878_;
v_isShared_2893_ = v_isSharedCheck_2907_;
goto v_resetjp_2891_;
}
else
{
lean_dec(v_traceState_2878_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2907_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_ref_2841_);
lean_ctor_set(v___x_2894_, 1, v_a_2873_);
v___x_2895_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2839_, v___x_2894_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2895_);
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2895_);
lean_ctor_set_uint64(v_reuseFailAlloc_2906_, sizeof(void*)*1, v_tid_2890_);
v___x_2897_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2899_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 4, v___x_2897_);
v___x_2899_ = v___x_2888_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_env_2879_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v_nextMacroScope_2880_);
lean_ctor_set(v_reuseFailAlloc_2905_, 2, v_ngen_2881_);
lean_ctor_set(v_reuseFailAlloc_2905_, 3, v_auxDeclNGen_2882_);
lean_ctor_set(v_reuseFailAlloc_2905_, 4, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2905_, 5, v_cache_2883_);
lean_ctor_set(v_reuseFailAlloc_2905_, 6, v_messages_2884_);
lean_ctor_set(v_reuseFailAlloc_2905_, 7, v_infoState_2885_);
lean_ctor_set(v_reuseFailAlloc_2905_, 8, v_snapshotTasks_2886_);
v___x_2899_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2900_ = lean_st_ref_set(v___y_2844_, v___x_2899_);
v___x_2901_ = lean_box(0);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2901_);
v___x_2903_ = v___x_2875_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2911_, lean_object* v_data_2912_, lean_object* v_ref_2913_, lean_object* v_msg_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2911_, v_data_2912_, v_ref_2913_, v_msg_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
return v_res_2918_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2921_ = l_Lean_stringToMessageData(v___x_2920_);
return v___x_2921_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2922_; double v___x_2923_; 
v___x_2922_ = lean_unsigned_to_nat(1000u);
v___x_2923_ = lean_float_of_nat(v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2924_, uint8_t v_collapsed_2925_, lean_object* v_tag_2926_, lean_object* v_opts_2927_, uint8_t v_clsEnabled_2928_, lean_object* v_oldTraces_2929_, lean_object* v_msg_2930_, lean_object* v_resStartStop_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_fst_2935_; lean_object* v_snd_2936_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v_data_2940_; lean_object* v_fst_2951_; lean_object* v_snd_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; lean_object* v___y_2956_; lean_object* v_a_2957_; uint8_t v___y_2972_; double v___y_3003_; 
v_fst_2935_ = lean_ctor_get(v_resStartStop_2931_, 0);
lean_inc(v_fst_2935_);
v_snd_2936_ = lean_ctor_get(v_resStartStop_2931_, 1);
lean_inc(v_snd_2936_);
lean_dec_ref(v_resStartStop_2931_);
v_fst_2951_ = lean_ctor_get(v_snd_2936_, 0);
lean_inc(v_fst_2951_);
v_snd_2952_ = lean_ctor_get(v_snd_2936_, 1);
lean_inc(v_snd_2952_);
lean_dec(v_snd_2936_);
v___x_2953_ = l_Lean_trace_profiler;
v___x_2954_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2927_, v___x_2953_);
if (v___x_2954_ == 0)
{
v___y_2972_ = v___x_2954_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3008_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3009_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2927_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; double v___x_3012_; double v___x_3013_; double v___x_3014_; 
v___x_3010_ = l_Lean_trace_profiler_threshold;
v___x_3011_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2927_, v___x_3010_);
v___x_3012_ = lean_float_of_nat(v___x_3011_);
v___x_3013_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3014_ = lean_float_div(v___x_3012_, v___x_3013_);
v___y_3003_ = v___x_3014_;
goto v___jp_3002_;
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; double v___x_3017_; 
v___x_3015_ = l_Lean_trace_profiler_threshold;
v___x_3016_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2927_, v___x_3015_);
v___x_3017_ = lean_float_of_nat(v___x_3016_);
v___y_3003_ = v___x_3017_;
goto v___jp_3002_;
}
}
v___jp_2937_:
{
lean_object* v___x_2941_; 
lean_inc(v___y_2939_);
v___x_2941_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2929_, v_data_2940_, v___y_2939_, v___y_2938_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2942_; 
lean_dec_ref_known(v___x_2941_, 1);
v___x_2942_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2935_);
return v___x_2942_;
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_fst_2935_);
v_a_2943_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2941_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2941_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
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
v___jp_2955_:
{
uint8_t v_result_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; double v___x_2961_; lean_object* v_data_2962_; 
v_result_2958_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2935_);
v___x_2959_ = lean_box(v_result_2958_);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
v___x_2961_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2926_);
lean_inc_ref(v___x_2960_);
lean_inc(v_cls_2924_);
v_data_2962_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2962_, 0, v_cls_2924_);
lean_ctor_set(v_data_2962_, 1, v___x_2960_);
lean_ctor_set(v_data_2962_, 2, v_tag_2926_);
lean_ctor_set_float(v_data_2962_, sizeof(void*)*3, v___x_2961_);
lean_ctor_set_float(v_data_2962_, sizeof(void*)*3 + 8, v___x_2961_);
lean_ctor_set_uint8(v_data_2962_, sizeof(void*)*3 + 16, v_collapsed_2925_);
if (v___x_2954_ == 0)
{
lean_dec_ref_known(v___x_2960_, 1);
lean_dec(v_snd_2952_);
lean_dec(v_fst_2951_);
lean_dec_ref(v_tag_2926_);
lean_dec(v_cls_2924_);
v___y_2938_ = v_a_2957_;
v___y_2939_ = v___y_2956_;
v_data_2940_ = v_data_2962_;
goto v___jp_2937_;
}
else
{
lean_object* v_data_2963_; double v___x_2964_; double v___x_2965_; 
lean_dec_ref_known(v_data_2962_, 3);
v_data_2963_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2963_, 0, v_cls_2924_);
lean_ctor_set(v_data_2963_, 1, v___x_2960_);
lean_ctor_set(v_data_2963_, 2, v_tag_2926_);
v___x_2964_ = lean_unbox_float(v_fst_2951_);
lean_dec(v_fst_2951_);
lean_ctor_set_float(v_data_2963_, sizeof(void*)*3, v___x_2964_);
v___x_2965_ = lean_unbox_float(v_snd_2952_);
lean_dec(v_snd_2952_);
lean_ctor_set_float(v_data_2963_, sizeof(void*)*3 + 8, v___x_2965_);
lean_ctor_set_uint8(v_data_2963_, sizeof(void*)*3 + 16, v_collapsed_2925_);
v___y_2938_ = v_a_2957_;
v___y_2939_ = v___y_2956_;
v_data_2940_ = v_data_2963_;
goto v___jp_2937_;
}
}
v___jp_2966_:
{
lean_object* v_ref_2967_; lean_object* v___x_2968_; 
v_ref_2967_ = lean_ctor_get(v___y_2932_, 5);
lean_inc(v___y_2933_);
lean_inc_ref(v___y_2932_);
lean_inc(v_fst_2935_);
v___x_2968_ = lean_apply_4(v_msg_2930_, v_fst_2935_, v___y_2932_, v___y_2933_, lean_box(0));
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v___y_2956_ = v_ref_2967_;
v_a_2957_ = v_a_2969_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2956_ = v_ref_2967_;
v_a_2957_ = v___x_2970_;
goto v___jp_2955_;
}
}
v___jp_2971_:
{
if (v_clsEnabled_2928_ == 0)
{
if (v___y_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v_traceState_2974_; lean_object* v_env_2975_; lean_object* v_nextMacroScope_2976_; lean_object* v_ngen_2977_; lean_object* v_auxDeclNGen_2978_; lean_object* v_cache_2979_; lean_object* v_messages_2980_; lean_object* v_infoState_2981_; lean_object* v_snapshotTasks_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v_snd_2952_);
lean_dec(v_fst_2951_);
lean_dec_ref(v_msg_2930_);
lean_dec_ref(v_tag_2926_);
lean_dec(v_cls_2924_);
v___x_2973_ = lean_st_ref_take(v___y_2933_);
v_traceState_2974_ = lean_ctor_get(v___x_2973_, 4);
v_env_2975_ = lean_ctor_get(v___x_2973_, 0);
v_nextMacroScope_2976_ = lean_ctor_get(v___x_2973_, 1);
v_ngen_2977_ = lean_ctor_get(v___x_2973_, 2);
v_auxDeclNGen_2978_ = lean_ctor_get(v___x_2973_, 3);
v_cache_2979_ = lean_ctor_get(v___x_2973_, 5);
v_messages_2980_ = lean_ctor_get(v___x_2973_, 6);
v_infoState_2981_ = lean_ctor_get(v___x_2973_, 7);
v_snapshotTasks_2982_ = lean_ctor_get(v___x_2973_, 8);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2984_ = v___x_2973_;
v_isShared_2985_ = v_isSharedCheck_3001_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_snapshotTasks_2982_);
lean_inc(v_infoState_2981_);
lean_inc(v_messages_2980_);
lean_inc(v_cache_2979_);
lean_inc(v_traceState_2974_);
lean_inc(v_auxDeclNGen_2978_);
lean_inc(v_ngen_2977_);
lean_inc(v_nextMacroScope_2976_);
lean_inc(v_env_2975_);
lean_dec(v___x_2973_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3001_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
uint64_t v_tid_2986_; lean_object* v_traces_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3000_; 
v_tid_2986_ = lean_ctor_get_uint64(v_traceState_2974_, sizeof(void*)*1);
v_traces_2987_ = lean_ctor_get(v_traceState_2974_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_traceState_2974_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2989_ = v_traceState_2974_;
v_isShared_2990_ = v_isSharedCheck_3000_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_traces_2987_);
lean_dec(v_traceState_2974_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3000_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2991_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2929_, v_traces_2987_);
lean_dec_ref(v_traces_2987_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2991_);
v___x_2993_ = v___x_2989_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2991_);
lean_ctor_set_uint64(v_reuseFailAlloc_2999_, sizeof(void*)*1, v_tid_2986_);
v___x_2993_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2995_; 
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 4, v___x_2993_);
v___x_2995_ = v___x_2984_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_env_2975_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_nextMacroScope_2976_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_ngen_2977_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v_auxDeclNGen_2978_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2998_, 5, v_cache_2979_);
lean_ctor_set(v_reuseFailAlloc_2998_, 6, v_messages_2980_);
lean_ctor_set(v_reuseFailAlloc_2998_, 7, v_infoState_2981_);
lean_ctor_set(v_reuseFailAlloc_2998_, 8, v_snapshotTasks_2982_);
v___x_2995_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_st_ref_set(v___y_2933_, v___x_2995_);
v___x_2997_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2935_);
return v___x_2997_;
}
}
}
}
}
else
{
goto v___jp_2966_;
}
}
else
{
goto v___jp_2966_;
}
}
v___jp_3002_:
{
double v___x_3004_; double v___x_3005_; double v___x_3006_; uint8_t v___x_3007_; 
v___x_3004_ = lean_unbox_float(v_snd_2952_);
v___x_3005_ = lean_unbox_float(v_fst_2951_);
v___x_3006_ = lean_float_sub(v___x_3004_, v___x_3005_);
v___x_3007_ = lean_float_decLt(v___y_3003_, v___x_3006_);
v___y_2972_ = v___x_3007_;
goto v___jp_2971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3018_, lean_object* v_collapsed_3019_, lean_object* v_tag_3020_, lean_object* v_opts_3021_, lean_object* v_clsEnabled_3022_, lean_object* v_oldTraces_3023_, lean_object* v_msg_3024_, lean_object* v_resStartStop_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
uint8_t v_collapsed_boxed_3029_; uint8_t v_clsEnabled_boxed_3030_; lean_object* v_res_3031_; 
v_collapsed_boxed_3029_ = lean_unbox(v_collapsed_3019_);
v_clsEnabled_boxed_3030_ = lean_unbox(v_clsEnabled_3022_);
v_res_3031_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3018_, v_collapsed_boxed_3029_, v_tag_3020_, v_opts_3021_, v_clsEnabled_boxed_3030_, v_oldTraces_3023_, v_msg_3024_, v_resStartStop_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v_opts_3021_);
return v_res_3031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
lean_ctor_set(v___x_3036_, 2, v___x_3035_);
lean_ctor_set(v___x_3036_, 3, v___x_3035_);
lean_ctor_set(v___x_3036_, 4, v___x_3034_);
lean_ctor_set(v___x_3036_, 5, v___x_3034_);
lean_ctor_set(v___x_3036_, 6, v___x_3034_);
lean_ctor_set(v___x_3036_, 7, v___x_3034_);
lean_ctor_set(v___x_3036_, 8, v___x_3034_);
lean_ctor_set(v___x_3036_, 9, v___x_3034_);
return v___x_3036_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3038_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
lean_ctor_set(v___x_3038_, 2, v___x_3037_);
lean_ctor_set(v___x_3038_, 3, v___x_3037_);
lean_ctor_set(v___x_3038_, 4, v___x_3037_);
lean_ctor_set(v___x_3038_, 5, v___x_3037_);
return v___x_3038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
lean_ctor_set(v___x_3040_, 2, v___x_3039_);
lean_ctor_set(v___x_3040_, 3, v___x_3039_);
lean_ctor_set(v___x_3040_, 4, v___x_3039_);
return v___x_3040_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3041_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3042_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3043_ = lean_box(1);
v___x_3044_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3045_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v___x_3044_);
lean_ctor_set(v___x_3046_, 2, v___x_3043_);
lean_ctor_set(v___x_3046_, 3, v___x_3042_);
lean_ctor_set(v___x_3046_, 4, v___x_3041_);
return v___x_3046_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3052_ = l_Lean_Name_append(v___x_3051_, v___x_3050_);
return v___x_3052_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3053_; double v___x_3054_; 
v___x_3053_ = lean_unsigned_to_nat(1000000000u);
v___x_3054_ = lean_float_of_nat(v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_3055_, lean_object* v_name_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_options_3060_; uint8_t v_hasTrace_3061_; 
v_options_3060_ = lean_ctor_get(v___y_3057_, 2);
v_hasTrace_3061_ = lean_ctor_get_uint8(v_options_3060_, sizeof(void*)*1);
if (v_hasTrace_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v_env_3063_; lean_object* v___x_3064_; 
lean_dec_ref(v___f_3055_);
v___x_3062_ = lean_st_ref_get(v___y_3058_);
v_env_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc_ref(v_env_3063_);
lean_dec(v___x_3062_);
lean_inc(v_name_3056_);
v___x_3064_ = l_Lean_Meta_declFromEqLikeName(v_env_3063_, v_name_3056_);
if (lean_obj_tag(v___x_3064_) == 1)
{
lean_object* v_val_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3164_; 
v_val_3065_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3067_ = v___x_3064_;
v_isShared_3068_ = v_isSharedCheck_3164_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_val_3065_);
lean_dec(v___x_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3164_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v_fst_3069_; lean_object* v_snd_3070_; lean_object* v___x_3071_; lean_object* v_env_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v_fst_3069_ = lean_ctor_get(v_val_3065_, 0);
lean_inc_n(v_fst_3069_, 2);
v_snd_3070_ = lean_ctor_get(v_val_3065_, 1);
lean_inc_n(v_snd_3070_, 2);
lean_dec(v_val_3065_);
v___x_3071_ = lean_st_ref_get(v___y_3058_);
v_env_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc_ref(v_env_3072_);
lean_dec(v___x_3071_);
v___x_3073_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3072_, v_fst_3069_, v_snd_3070_);
v___x_3074_ = lean_name_eq(v_name_3056_, v___x_3073_);
lean_dec(v___x_3073_);
lean_dec(v_name_3056_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3077_; 
lean_dec(v_snd_3070_);
lean_dec(v_fst_3069_);
v___x_3075_ = lean_box(v_hasTrace_3061_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3075_);
v___x_3077_ = v___x_3067_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
else
{
uint8_t v___x_3079_; lean_object* v_a_3081_; 
lean_inc(v_snd_3070_);
v___x_3079_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3070_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3095_; uint8_t v___x_3096_; lean_object* v_a_3098_; 
lean_del_object(v___x_3067_);
v___x_3095_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3096_ = lean_string_dec_eq(v_snd_3070_, v___x_3095_);
lean_dec(v_snd_3070_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec(v_fst_3069_);
v___x_3110_ = lean_box(v_hasTrace_3061_);
v___x_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
else
{
uint8_t v___x_3112_; uint8_t v___x_3113_; uint8_t v___x_3114_; lean_object* v___x_3115_; uint64_t v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3112_ = 1;
v___x_3113_ = 0;
v___x_3114_ = 2;
v___x_3115_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3115_, 0, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3115_, 1, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3115_, 2, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3115_, 3, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3115_, 4, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3115_, 5, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 6, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 7, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3115_, 8, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 9, v___x_3112_);
lean_ctor_set_uint8(v___x_3115_, 10, v___x_3113_);
lean_ctor_set_uint8(v___x_3115_, 11, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 12, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 13, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 14, v___x_3114_);
lean_ctor_set_uint8(v___x_3115_, 15, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 16, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 17, v___x_3096_);
lean_ctor_set_uint8(v___x_3115_, 18, v___x_3096_);
v___x_3116_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3115_);
v___x_3117_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set_uint64(v___x_3117_, sizeof(void*)*1, v___x_3116_);
v___x_3118_ = lean_box(1);
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3121_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3122_ = lean_box(0);
v___x_3123_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3123_, 0, v___x_3117_);
lean_ctor_set(v___x_3123_, 1, v___x_3118_);
lean_ctor_set(v___x_3123_, 2, v___x_3120_);
lean_ctor_set(v___x_3123_, 3, v___x_3121_);
lean_ctor_set(v___x_3123_, 4, v___x_3122_);
lean_ctor_set(v___x_3123_, 5, v___x_3119_);
lean_ctor_set(v___x_3123_, 6, v___x_3122_);
lean_ctor_set_uint8(v___x_3123_, sizeof(void*)*7, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3123_, sizeof(void*)*7 + 1, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3123_, sizeof(void*)*7 + 2, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3123_, sizeof(void*)*7 + 3, v___x_3074_);
v___x_3124_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3125_ = lean_st_mk_ref(v___x_3124_);
v___x_3126_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3069_, v___x_3074_, v___x_3123_, v___x_3125_, v___y_3057_, v___y_3058_);
lean_dec_ref_known(v___x_3123_, 7);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3128_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v___x_3128_ = lean_st_ref_get(v___x_3125_);
lean_dec(v___x_3125_);
lean_dec(v___x_3128_);
v_a_3098_ = v_a_3127_;
goto v___jp_3097_;
}
else
{
lean_dec(v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3129_; 
v_a_3129_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3126_, 1);
v_a_3098_ = v_a_3129_;
goto v___jp_3097_;
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
v_a_3130_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3126_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3126_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
v___jp_3097_:
{
if (lean_obj_tag(v_a_3098_) == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_box(v_hasTrace_3061_);
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
return v___x_3100_;
}
else
{
lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3108_; 
v_isSharedCheck_3108_ = !lean_is_exclusive(v_a_3098_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; 
v_unused_3109_ = lean_ctor_get(v_a_3098_, 0);
lean_dec(v_unused_3109_);
v___x_3102_ = v_a_3098_;
v_isShared_3103_ = v_isSharedCheck_3108_;
goto v_resetjp_3101_;
}
else
{
lean_dec(v_a_3098_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3108_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3104_ = lean_box(v___x_3096_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3104_);
v___x_3106_ = v___x_3102_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
else
{
uint8_t v___x_3138_; uint8_t v___x_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; uint64_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec(v_snd_3070_);
v___x_3138_ = 1;
v___x_3139_ = 0;
v___x_3140_ = 2;
v___x_3141_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3141_, 0, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3141_, 1, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3141_, 2, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3141_, 3, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3141_, 4, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3141_, 5, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 6, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 7, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3141_, 8, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 9, v___x_3138_);
lean_ctor_set_uint8(v___x_3141_, 10, v___x_3139_);
lean_ctor_set_uint8(v___x_3141_, 11, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 12, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 13, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 14, v___x_3140_);
lean_ctor_set_uint8(v___x_3141_, 15, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 16, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 17, v___x_3079_);
lean_ctor_set_uint8(v___x_3141_, 18, v___x_3079_);
v___x_3142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3141_);
v___x_3143_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3143_, 0, v___x_3141_);
lean_ctor_set_uint64(v___x_3143_, sizeof(void*)*1, v___x_3142_);
v___x_3144_ = lean_box(1);
v___x_3145_ = lean_unsigned_to_nat(0u);
v___x_3146_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3147_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3148_ = lean_box(0);
v___x_3149_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3149_, 0, v___x_3143_);
lean_ctor_set(v___x_3149_, 1, v___x_3144_);
lean_ctor_set(v___x_3149_, 2, v___x_3146_);
lean_ctor_set(v___x_3149_, 3, v___x_3147_);
lean_ctor_set(v___x_3149_, 4, v___x_3148_);
lean_ctor_set(v___x_3149_, 5, v___x_3145_);
lean_ctor_set(v___x_3149_, 6, v___x_3148_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*7, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*7 + 1, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*7 + 2, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*7 + 3, v___x_3074_);
v___x_3150_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3151_ = lean_st_mk_ref(v___x_3150_);
v___x_3152_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3069_, v___x_3149_, v___x_3151_, v___y_3057_, v___y_3058_);
lean_dec_ref_known(v___x_3149_, 7);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3154_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3154_ = lean_st_ref_get(v___x_3151_);
lean_dec(v___x_3151_);
lean_dec(v___x_3154_);
v_a_3081_ = v_a_3153_;
goto v___jp_3080_;
}
else
{
lean_dec(v___x_3151_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3155_; 
v_a_3155_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3152_, 1);
v_a_3081_ = v_a_3155_;
goto v___jp_3080_;
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_del_object(v___x_3067_);
v_a_3156_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3152_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3152_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
v___jp_3080_:
{
if (lean_obj_tag(v_a_3081_) == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = lean_box(v_hasTrace_3061_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3082_);
v___x_3084_ = v___x_3067_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
else
{
lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3093_; 
lean_del_object(v___x_3067_);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_a_3081_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; 
v_unused_3094_ = lean_ctor_get(v_a_3081_, 0);
lean_dec(v_unused_3094_);
v___x_3087_ = v_a_3081_;
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
else
{
lean_dec(v_a_3081_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_box(v___x_3079_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 0);
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
}
}
}
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_dec(v___x_3064_);
lean_dec(v_name_3056_);
v___x_3165_ = lean_box(v_hasTrace_3061_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v_a_3176_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v_a_3191_; lean_object* v___y_3195_; uint8_t v___y_3196_; lean_object* v___y_3197_; lean_object* v_a_3198_; lean_object* v___y_3200_; uint8_t v___y_3201_; lean_object* v___y_3202_; lean_object* v_a_3203_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v_a_3207_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v_a_3212_; lean_object* v___y_3222_; lean_object* v___y_3223_; uint8_t v_a_3224_; uint8_t v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v_a_3232_; uint8_t v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v_a_3237_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v_a_3242_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; 
v_inheritedTraceOptions_3167_ = lean_ctor_get(v___y_3057_, 13);
lean_inc(v_name_3056_);
v___f_3168_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3168_, 0, v_name_3056_);
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3170_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3171_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3172_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3167_, v_options_3060_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3367_; uint8_t v___x_3368_; lean_object* v_a_3370_; lean_object* v_a_3383_; 
v___x_3367_ = l_Lean_trace_profiler;
v___x_3368_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3060_, v___x_3367_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3395_; lean_object* v_env_3396_; lean_object* v___x_3397_; 
lean_dec_ref(v___f_3168_);
lean_dec_ref(v___f_3055_);
v___x_3395_ = lean_st_ref_get(v___y_3058_);
v_env_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc_ref(v_env_3396_);
lean_dec(v___x_3395_);
lean_inc(v_name_3056_);
v___x_3397_ = l_Lean_Meta_declFromEqLikeName(v_env_3396_, v_name_3056_);
if (lean_obj_tag(v___x_3397_) == 1)
{
lean_object* v_val_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3471_; 
v_val_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3471_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_val_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3471_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v_fst_3402_; lean_object* v_snd_3403_; lean_object* v___x_3404_; lean_object* v_env_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v_fst_3402_ = lean_ctor_get(v_val_3398_, 0);
lean_inc_n(v_fst_3402_, 2);
v_snd_3403_ = lean_ctor_get(v_val_3398_, 1);
lean_inc_n(v_snd_3403_, 2);
lean_dec(v_val_3398_);
v___x_3404_ = lean_st_ref_get(v___y_3058_);
v_env_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc_ref(v_env_3405_);
lean_dec(v___x_3404_);
v___x_3406_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3405_, v_fst_3402_, v_snd_3403_);
v___x_3407_ = lean_name_eq(v_name_3056_, v___x_3406_);
lean_dec(v___x_3406_);
lean_dec(v_name_3056_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3410_; 
lean_dec(v_snd_3403_);
lean_dec(v_fst_3402_);
v___x_3408_ = lean_box(v___x_3368_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3408_);
v___x_3410_ = v___x_3400_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
else
{
uint8_t v___x_3412_; 
lean_inc(v_snd_3403_);
v___x_3412_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3403_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3413_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3414_ = lean_string_dec_eq(v_snd_3403_, v___x_3413_);
lean_dec(v_snd_3403_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
lean_dec(v_fst_3402_);
v___x_3415_ = lean_box(v___x_3368_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3415_);
v___x_3417_ = v___x_3400_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
else
{
uint8_t v___x_3419_; uint8_t v___x_3420_; uint8_t v___x_3421_; lean_object* v___x_3422_; uint64_t v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_del_object(v___x_3400_);
v___x_3419_ = 1;
v___x_3420_ = 0;
v___x_3421_ = 2;
v___x_3422_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3422_, 0, v___x_3368_);
lean_ctor_set_uint8(v___x_3422_, 1, v___x_3368_);
lean_ctor_set_uint8(v___x_3422_, 2, v___x_3368_);
lean_ctor_set_uint8(v___x_3422_, 3, v___x_3368_);
lean_ctor_set_uint8(v___x_3422_, 4, v___x_3368_);
lean_ctor_set_uint8(v___x_3422_, 5, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 6, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 7, v___x_3368_);
lean_ctor_set_uint8(v___x_3422_, 8, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 9, v___x_3419_);
lean_ctor_set_uint8(v___x_3422_, 10, v___x_3420_);
lean_ctor_set_uint8(v___x_3422_, 11, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 12, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 13, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 14, v___x_3421_);
lean_ctor_set_uint8(v___x_3422_, 15, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 16, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 17, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3422_, 18, v_hasTrace_3061_);
v___x_3423_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3422_);
v___x_3424_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set_uint64(v___x_3424_, sizeof(void*)*1, v___x_3423_);
v___x_3425_ = lean_box(1);
v___x_3426_ = lean_unsigned_to_nat(0u);
v___x_3427_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3429_ = lean_box(0);
v___x_3430_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3430_, 0, v___x_3424_);
lean_ctor_set(v___x_3430_, 1, v___x_3425_);
lean_ctor_set(v___x_3430_, 2, v___x_3427_);
lean_ctor_set(v___x_3430_, 3, v___x_3428_);
lean_ctor_set(v___x_3430_, 4, v___x_3429_);
lean_ctor_set(v___x_3430_, 5, v___x_3426_);
lean_ctor_set(v___x_3430_, 6, v___x_3429_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*7, v___x_3368_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*7 + 1, v___x_3368_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*7 + 2, v___x_3368_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*7 + 3, v_hasTrace_3061_);
v___x_3431_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3432_ = lean_st_mk_ref(v___x_3431_);
v___x_3433_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3402_, v_hasTrace_3061_, v___x_3430_, v___x_3432_, v___y_3057_, v___y_3058_);
lean_dec_ref_known(v___x_3430_, 7);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3435_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v___x_3435_ = lean_st_ref_get(v___x_3432_);
lean_dec(v___x_3432_);
lean_dec(v___x_3435_);
v_a_3383_ = v_a_3434_;
goto v___jp_3382_;
}
else
{
lean_dec(v___x_3432_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3436_; 
v_a_3436_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3433_, 1);
v_a_3383_ = v_a_3436_;
goto v___jp_3382_;
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
v_a_3437_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3433_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3433_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
}
else
{
uint8_t v___x_3445_; uint8_t v___x_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; uint64_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec(v_snd_3403_);
lean_del_object(v___x_3400_);
v___x_3445_ = 1;
v___x_3446_ = 0;
v___x_3447_ = 2;
v___x_3448_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3448_, 0, v___x_3368_);
lean_ctor_set_uint8(v___x_3448_, 1, v___x_3368_);
lean_ctor_set_uint8(v___x_3448_, 2, v___x_3368_);
lean_ctor_set_uint8(v___x_3448_, 3, v___x_3368_);
lean_ctor_set_uint8(v___x_3448_, 4, v___x_3368_);
lean_ctor_set_uint8(v___x_3448_, 5, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 6, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 7, v___x_3368_);
lean_ctor_set_uint8(v___x_3448_, 8, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 9, v___x_3445_);
lean_ctor_set_uint8(v___x_3448_, 10, v___x_3446_);
lean_ctor_set_uint8(v___x_3448_, 11, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 12, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 13, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 14, v___x_3447_);
lean_ctor_set_uint8(v___x_3448_, 15, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 16, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 17, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3448_, 18, v_hasTrace_3061_);
v___x_3449_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3448_);
v___x_3450_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set_uint64(v___x_3450_, sizeof(void*)*1, v___x_3449_);
v___x_3451_ = lean_box(1);
v___x_3452_ = lean_unsigned_to_nat(0u);
v___x_3453_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3454_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3456_, 0, v___x_3450_);
lean_ctor_set(v___x_3456_, 1, v___x_3451_);
lean_ctor_set(v___x_3456_, 2, v___x_3453_);
lean_ctor_set(v___x_3456_, 3, v___x_3454_);
lean_ctor_set(v___x_3456_, 4, v___x_3455_);
lean_ctor_set(v___x_3456_, 5, v___x_3452_);
lean_ctor_set(v___x_3456_, 6, v___x_3455_);
lean_ctor_set_uint8(v___x_3456_, sizeof(void*)*7, v___x_3368_);
lean_ctor_set_uint8(v___x_3456_, sizeof(void*)*7 + 1, v___x_3368_);
lean_ctor_set_uint8(v___x_3456_, sizeof(void*)*7 + 2, v___x_3368_);
lean_ctor_set_uint8(v___x_3456_, sizeof(void*)*7 + 3, v_hasTrace_3061_);
v___x_3457_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3458_ = lean_st_mk_ref(v___x_3457_);
v___x_3459_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3402_, v___x_3456_, v___x_3458_, v___y_3057_, v___y_3058_);
lean_dec_ref_known(v___x_3456_, 7);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v___x_3461_ = lean_st_ref_get(v___x_3458_);
lean_dec(v___x_3458_);
lean_dec(v___x_3461_);
v_a_3370_ = v_a_3460_;
goto v___jp_3369_;
}
else
{
lean_dec(v___x_3458_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3462_; 
v_a_3462_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3459_, 1);
v_a_3370_ = v_a_3462_;
goto v___jp_3369_;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
v_a_3463_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3459_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3459_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
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
lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_dec(v___x_3397_);
lean_dec(v_name_3056_);
v___x_3472_ = lean_box(v___x_3368_);
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
return v___x_3473_;
}
}
else
{
goto v___jp_3251_;
}
v___jp_3369_:
{
if (lean_obj_tag(v_a_3370_) == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_box(v___x_3368_);
v___x_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
return v___x_3372_;
}
else
{
lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3380_; 
v_isSharedCheck_3380_ = !lean_is_exclusive(v_a_3370_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v_a_3370_, 0);
lean_dec(v_unused_3381_);
v___x_3374_ = v_a_3370_;
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
else
{
lean_dec(v_a_3370_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
v___x_3376_ = lean_box(v_hasTrace_3061_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3376_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
v___jp_3382_:
{
if (lean_obj_tag(v_a_3383_) == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_box(v___x_3368_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
return v___x_3385_;
}
else
{
lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3393_; 
v_isSharedCheck_3393_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; 
v_unused_3394_ = lean_ctor_get(v_a_3383_, 0);
lean_dec(v_unused_3394_);
v___x_3387_ = v_a_3383_;
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
else
{
lean_dec(v_a_3383_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_box(v_hasTrace_3061_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set_tag(v___x_3387_, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3389_);
v___x_3391_ = v___x_3387_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
else
{
goto v___jp_3251_;
}
v___jp_3173_:
{
lean_object* v___x_3177_; double v___x_3178_; double v___x_3179_; double v___x_3180_; double v___x_3181_; double v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3177_ = lean_io_mono_nanos_now();
v___x_3178_ = lean_float_of_nat(v___y_3174_);
v___x_3179_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3180_ = lean_float_div(v___x_3178_, v___x_3179_);
v___x_3181_ = lean_float_of_nat(v___x_3177_);
v___x_3182_ = lean_float_div(v___x_3181_, v___x_3179_);
v___x_3183_ = lean_box_float(v___x_3180_);
v___x_3184_ = lean_box_float(v___x_3182_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v_a_3176_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3169_, v_hasTrace_3061_, v___x_3170_, v_options_3060_, v___x_3172_, v___y_3175_, v___f_3168_, v___x_3186_, v___y_3057_, v___y_3058_);
return v___x_3187_;
}
v___jp_3188_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = lean_box(v_a_3191_);
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
v___y_3174_ = v___y_3189_;
v___y_3175_ = v___y_3190_;
v_a_3176_ = v___x_3193_;
goto v___jp_3173_;
}
v___jp_3194_:
{
if (lean_obj_tag(v_a_3198_) == 0)
{
v___y_3189_ = v___y_3195_;
v___y_3190_ = v___y_3197_;
v_a_3191_ = v___y_3196_;
goto v___jp_3188_;
}
else
{
lean_dec_ref_known(v_a_3198_, 1);
v___y_3189_ = v___y_3195_;
v___y_3190_ = v___y_3197_;
v_a_3191_ = v_hasTrace_3061_;
goto v___jp_3188_;
}
}
v___jp_3199_:
{
if (lean_obj_tag(v_a_3203_) == 0)
{
v___y_3189_ = v___y_3200_;
v___y_3190_ = v___y_3202_;
v_a_3191_ = v___y_3201_;
goto v___jp_3188_;
}
else
{
lean_dec_ref_known(v_a_3203_, 1);
v___y_3189_ = v___y_3200_;
v___y_3190_ = v___y_3202_;
v_a_3191_ = v_hasTrace_3061_;
goto v___jp_3188_;
}
}
v___jp_3204_:
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v_a_3207_);
v___y_3174_ = v___y_3205_;
v___y_3175_ = v___y_3206_;
v_a_3176_ = v___x_3208_;
goto v___jp_3173_;
}
v___jp_3209_:
{
lean_object* v___x_3213_; double v___x_3214_; double v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3213_ = lean_io_get_num_heartbeats();
v___x_3214_ = lean_float_of_nat(v___y_3210_);
v___x_3215_ = lean_float_of_nat(v___x_3213_);
v___x_3216_ = lean_box_float(v___x_3214_);
v___x_3217_ = lean_box_float(v___x_3215_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_a_3212_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3169_, v_hasTrace_3061_, v___x_3170_, v_options_3060_, v___x_3172_, v___y_3211_, v___f_3168_, v___x_3219_, v___y_3057_, v___y_3058_);
return v___x_3220_;
}
v___jp_3221_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = lean_box(v_a_3224_);
v___x_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
v___y_3210_ = v___y_3222_;
v___y_3211_ = v___y_3223_;
v_a_3212_ = v___x_3226_;
goto v___jp_3209_;
}
v___jp_3227_:
{
if (lean_obj_tag(v_a_3232_) == 0)
{
v___y_3222_ = v___y_3230_;
v___y_3223_ = v___y_3231_;
v_a_3224_ = v___y_3229_;
goto v___jp_3221_;
}
else
{
lean_dec_ref_known(v_a_3232_, 1);
v___y_3222_ = v___y_3230_;
v___y_3223_ = v___y_3231_;
v_a_3224_ = v___y_3228_;
goto v___jp_3221_;
}
}
v___jp_3233_:
{
if (lean_obj_tag(v_a_3237_) == 0)
{
uint8_t v___x_3238_; 
v___x_3238_ = 0;
v___y_3222_ = v___y_3235_;
v___y_3223_ = v___y_3236_;
v_a_3224_ = v___x_3238_;
goto v___jp_3221_;
}
else
{
lean_dec_ref_known(v_a_3237_, 1);
v___y_3222_ = v___y_3235_;
v___y_3223_ = v___y_3236_;
v_a_3224_ = v___y_3234_;
goto v___jp_3221_;
}
}
v___jp_3239_:
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3243_, 0, v_a_3242_);
v___y_3210_ = v___y_3240_;
v___y_3211_ = v___y_3241_;
v_a_3212_ = v___x_3243_;
goto v___jp_3209_;
}
v___jp_3244_:
{
if (lean_obj_tag(v___y_3247_) == 0)
{
lean_object* v_a_3248_; uint8_t v___x_3249_; 
v_a_3248_ = lean_ctor_get(v___y_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___y_3247_, 1);
v___x_3249_ = lean_unbox(v_a_3248_);
lean_dec(v_a_3248_);
v___y_3222_ = v___y_3245_;
v___y_3223_ = v___y_3246_;
v_a_3224_ = v___x_3249_;
goto v___jp_3221_;
}
else
{
lean_object* v_a_3250_; 
v_a_3250_ = lean_ctor_get(v___y_3247_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___y_3247_, 1);
v___y_3240_ = v___y_3245_;
v___y_3241_ = v___y_3246_;
v_a_3242_ = v_a_3250_;
goto v___jp_3239_;
}
}
v___jp_3251_:
{
lean_object* v___x_3252_; lean_object* v_a_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3252_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3058_);
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3252_);
v___x_3254_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3255_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3060_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v_env_3258_; lean_object* v___x_3259_; 
lean_dec_ref(v___f_3055_);
v___x_3256_ = lean_io_mono_nanos_now();
v___x_3257_ = lean_st_ref_get(v___y_3058_);
v_env_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc_ref(v_env_3258_);
lean_dec(v___x_3257_);
lean_inc(v_name_3056_);
v___x_3259_ = l_Lean_Meta_declFromEqLikeName(v_env_3258_, v_name_3056_);
if (lean_obj_tag(v___x_3259_) == 1)
{
lean_object* v_val_3260_; lean_object* v_fst_3261_; lean_object* v_snd_3262_; lean_object* v___x_3263_; lean_object* v_env_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v_val_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_val_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v_fst_3261_ = lean_ctor_get(v_val_3260_, 0);
lean_inc_n(v_fst_3261_, 2);
v_snd_3262_ = lean_ctor_get(v_val_3260_, 1);
lean_inc_n(v_snd_3262_, 2);
lean_dec(v_val_3260_);
v___x_3263_ = lean_st_ref_get(v___y_3058_);
v_env_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_ref(v_env_3264_);
lean_dec(v___x_3263_);
v___x_3265_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3264_, v_fst_3261_, v_snd_3262_);
v___x_3266_ = lean_name_eq(v_name_3056_, v___x_3265_);
lean_dec(v___x_3265_);
lean_dec(v_name_3056_);
if (v___x_3266_ == 0)
{
lean_dec(v_snd_3262_);
lean_dec(v_fst_3261_);
v___y_3189_ = v___x_3256_;
v___y_3190_ = v_a_3253_;
v_a_3191_ = v___x_3255_;
goto v___jp_3188_;
}
else
{
uint8_t v___x_3267_; 
lean_inc(v_snd_3262_);
v___x_3267_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3262_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3268_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3269_ = lean_string_dec_eq(v_snd_3262_, v___x_3268_);
lean_dec(v_snd_3262_);
if (v___x_3269_ == 0)
{
lean_dec(v_fst_3261_);
v___y_3189_ = v___x_3256_;
v___y_3190_ = v_a_3253_;
v_a_3191_ = v___x_3255_;
goto v___jp_3188_;
}
else
{
uint8_t v___x_3270_; uint8_t v___x_3271_; uint8_t v___x_3272_; lean_object* v___x_3273_; uint64_t v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3270_ = 1;
v___x_3271_ = 0;
v___x_3272_ = 2;
v___x_3273_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3273_, 0, v___x_3255_);
lean_ctor_set_uint8(v___x_3273_, 1, v___x_3255_);
lean_ctor_set_uint8(v___x_3273_, 2, v___x_3255_);
lean_ctor_set_uint8(v___x_3273_, 3, v___x_3255_);
lean_ctor_set_uint8(v___x_3273_, 4, v___x_3255_);
lean_ctor_set_uint8(v___x_3273_, 5, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 6, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 7, v___x_3255_);
lean_ctor_set_uint8(v___x_3273_, 8, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 9, v___x_3270_);
lean_ctor_set_uint8(v___x_3273_, 10, v___x_3271_);
lean_ctor_set_uint8(v___x_3273_, 11, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 12, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 13, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 14, v___x_3272_);
lean_ctor_set_uint8(v___x_3273_, 15, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 16, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 17, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3273_, 18, v_hasTrace_3061_);
v___x_3274_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3273_);
v___x_3275_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set_uint64(v___x_3275_, sizeof(void*)*1, v___x_3274_);
v___x_3276_ = lean_box(1);
v___x_3277_ = lean_unsigned_to_nat(0u);
v___x_3278_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3279_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3280_ = lean_box(0);
v___x_3281_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3281_, 0, v___x_3275_);
lean_ctor_set(v___x_3281_, 1, v___x_3276_);
lean_ctor_set(v___x_3281_, 2, v___x_3278_);
lean_ctor_set(v___x_3281_, 3, v___x_3279_);
lean_ctor_set(v___x_3281_, 4, v___x_3280_);
lean_ctor_set(v___x_3281_, 5, v___x_3277_);
lean_ctor_set(v___x_3281_, 6, v___x_3280_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*7, v___x_3255_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*7 + 1, v___x_3255_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*7 + 2, v___x_3255_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*7 + 3, v_hasTrace_3061_);
v___x_3282_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3283_ = lean_st_mk_ref(v___x_3282_);
v___x_3284_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3261_, v_hasTrace_3061_, v___x_3281_, v___x_3283_, v___y_3057_, v___y_3058_);
lean_dec_ref_known(v___x_3281_, 7);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = lean_st_ref_get(v___x_3283_);
lean_dec(v___x_3283_);
lean_dec(v___x_3286_);
v___y_3200_ = v___x_3256_;
v___y_3201_ = v___x_3255_;
v___y_3202_ = v_a_3253_;
v_a_3203_ = v_a_3285_;
goto v___jp_3199_;
}
else
{
lean_dec(v___x_3283_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3287_; 
v_a_3287_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3284_, 1);
v___y_3200_ = v___x_3256_;
v___y_3201_ = v___x_3255_;
v___y_3202_ = v_a_3253_;
v_a_3203_ = v_a_3287_;
goto v___jp_3199_;
}
else
{
lean_object* v_a_3288_; 
v_a_3288_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3284_, 1);
v___y_3205_ = v___x_3256_;
v___y_3206_ = v_a_3253_;
v_a_3207_ = v_a_3288_;
goto v___jp_3204_;
}
}
}
}
else
{
uint8_t v___x_3289_; uint8_t v___x_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; uint64_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec(v_snd_3262_);
v___x_3289_ = 1;
v___x_3290_ = 0;
v___x_3291_ = 2;
v___x_3292_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3292_, 0, v___x_3255_);
lean_ctor_set_uint8(v___x_3292_, 1, v___x_3255_);
lean_ctor_set_uint8(v___x_3292_, 2, v___x_3255_);
lean_ctor_set_uint8(v___x_3292_, 3, v___x_3255_);
lean_ctor_set_uint8(v___x_3292_, 4, v___x_3255_);
lean_ctor_set_uint8(v___x_3292_, 5, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 6, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 7, v___x_3255_);
lean_ctor_set_uint8(v___x_3292_, 8, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 9, v___x_3289_);
lean_ctor_set_uint8(v___x_3292_, 10, v___x_3290_);
lean_ctor_set_uint8(v___x_3292_, 11, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 12, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 13, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 14, v___x_3291_);
lean_ctor_set_uint8(v___x_3292_, 15, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 16, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 17, v_hasTrace_3061_);
lean_ctor_set_uint8(v___x_3292_, 18, v_hasTrace_3061_);
v___x_3293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3292_);
v___x_3294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set_uint64(v___x_3294_, sizeof(void*)*1, v___x_3293_);
v___x_3295_ = lean_box(1);
v___x_3296_ = lean_unsigned_to_nat(0u);
v___x_3297_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3298_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3300_, 0, v___x_3294_);
lean_ctor_set(v___x_3300_, 1, v___x_3295_);
lean_ctor_set(v___x_3300_, 2, v___x_3297_);
lean_ctor_set(v___x_3300_, 3, v___x_3298_);
lean_ctor_set(v___x_3300_, 4, v___x_3299_);
lean_ctor_set(v___x_3300_, 5, v___x_3296_);
lean_ctor_set(v___x_3300_, 6, v___x_3299_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7, v___x_3255_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 1, v___x_3255_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 2, v___x_3255_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 3, v_hasTrace_3061_);
v___x_3301_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3302_ = lean_st_mk_ref(v___x_3301_);
v___x_3303_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3261_, v___x_3300_, v___x_3302_, v___y_3057_, v___y_3058_);
lean_dec_ref_known(v___x_3300_, 7);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3303_, 1);
v___x_3305_ = lean_st_ref_get(v___x_3302_);
lean_dec(v___x_3302_);
lean_dec(v___x_3305_);
v___y_3195_ = v___x_3256_;
v___y_3196_ = v___x_3255_;
v___y_3197_ = v_a_3253_;
v_a_3198_ = v_a_3304_;
goto v___jp_3194_;
}
else
{
lean_dec(v___x_3302_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3306_; 
v_a_3306_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3303_, 1);
v___y_3195_ = v___x_3256_;
v___y_3196_ = v___x_3255_;
v___y_3197_ = v_a_3253_;
v_a_3198_ = v_a_3306_;
goto v___jp_3194_;
}
else
{
lean_object* v_a_3307_; 
v_a_3307_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3303_, 1);
v___y_3205_ = v___x_3256_;
v___y_3206_ = v_a_3253_;
v_a_3207_ = v_a_3307_;
goto v___jp_3204_;
}
}
}
}
}
else
{
lean_dec(v___x_3259_);
lean_dec(v_name_3056_);
v___y_3189_ = v___x_3256_;
v___y_3190_ = v_a_3253_;
v_a_3191_ = v___x_3255_;
goto v___jp_3188_;
}
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v_env_3310_; lean_object* v___x_3311_; 
v___x_3308_ = lean_io_get_num_heartbeats();
v___x_3309_ = lean_st_ref_get(v___y_3058_);
v_env_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc_ref(v_env_3310_);
lean_dec(v___x_3309_);
lean_inc(v_name_3056_);
v___x_3311_ = l_Lean_Meta_declFromEqLikeName(v_env_3310_, v_name_3056_);
if (lean_obj_tag(v___x_3311_) == 1)
{
lean_object* v_val_3312_; lean_object* v_fst_3313_; lean_object* v_snd_3314_; lean_object* v___x_3315_; lean_object* v_env_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v_val_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_val_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v_fst_3313_ = lean_ctor_get(v_val_3312_, 0);
lean_inc_n(v_fst_3313_, 2);
v_snd_3314_ = lean_ctor_get(v_val_3312_, 1);
lean_inc_n(v_snd_3314_, 2);
lean_dec(v_val_3312_);
v___x_3315_ = lean_st_ref_get(v___y_3058_);
v_env_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc_ref(v_env_3316_);
lean_dec(v___x_3315_);
v___x_3317_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3316_, v_fst_3313_, v_snd_3314_);
v___x_3318_ = lean_name_eq(v_name_3056_, v___x_3317_);
lean_dec(v___x_3317_);
lean_dec(v_name_3056_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec(v_snd_3314_);
lean_dec(v_fst_3313_);
v___x_3319_ = lean_box(0);
lean_inc(v___y_3058_);
lean_inc_ref(v___y_3057_);
v___x_3320_ = lean_apply_4(v___f_3055_, v___x_3319_, v___y_3057_, v___y_3058_, lean_box(0));
v___y_3245_ = v___x_3308_;
v___y_3246_ = v_a_3253_;
v___y_3247_ = v___x_3320_;
goto v___jp_3244_;
}
else
{
uint8_t v___x_3321_; 
lean_inc(v_snd_3314_);
v___x_3321_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3314_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3322_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3323_ = lean_string_dec_eq(v_snd_3314_, v___x_3322_);
lean_dec(v_snd_3314_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec(v_fst_3313_);
v___x_3324_ = lean_box(0);
lean_inc(v___y_3058_);
lean_inc_ref(v___y_3057_);
v___x_3325_ = lean_apply_4(v___f_3055_, v___x_3324_, v___y_3057_, v___y_3058_, lean_box(0));
v___y_3245_ = v___x_3308_;
v___y_3246_ = v_a_3253_;
v___y_3247_ = v___x_3325_;
goto v___jp_3244_;
}
else
{
uint8_t v___x_3326_; uint8_t v___x_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; uint64_t v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_dec_ref(v___f_3055_);
v___x_3326_ = 1;
v___x_3327_ = 0;
v___x_3328_ = 2;
v___x_3329_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3329_, 0, v___x_3321_);
lean_ctor_set_uint8(v___x_3329_, 1, v___x_3321_);
lean_ctor_set_uint8(v___x_3329_, 2, v___x_3321_);
lean_ctor_set_uint8(v___x_3329_, 3, v___x_3321_);
lean_ctor_set_uint8(v___x_3329_, 4, v___x_3321_);
lean_ctor_set_uint8(v___x_3329_, 5, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 6, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 7, v___x_3321_);
lean_ctor_set_uint8(v___x_3329_, 8, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 9, v___x_3326_);
lean_ctor_set_uint8(v___x_3329_, 10, v___x_3327_);
lean_ctor_set_uint8(v___x_3329_, 11, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 12, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 13, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 14, v___x_3328_);
lean_ctor_set_uint8(v___x_3329_, 15, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 16, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 17, v___x_3255_);
lean_ctor_set_uint8(v___x_3329_, 18, v___x_3255_);
v___x_3330_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3329_);
v___x_3331_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set_uint64(v___x_3331_, sizeof(void*)*1, v___x_3330_);
v___x_3332_ = lean_box(1);
v___x_3333_ = lean_unsigned_to_nat(0u);
v___x_3334_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3335_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3336_ = lean_box(0);
v___x_3337_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3337_, 0, v___x_3331_);
lean_ctor_set(v___x_3337_, 1, v___x_3332_);
lean_ctor_set(v___x_3337_, 2, v___x_3334_);
lean_ctor_set(v___x_3337_, 3, v___x_3335_);
lean_ctor_set(v___x_3337_, 4, v___x_3336_);
lean_ctor_set(v___x_3337_, 5, v___x_3333_);
lean_ctor_set(v___x_3337_, 6, v___x_3336_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*7, v___x_3321_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*7 + 1, v___x_3321_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*7 + 2, v___x_3321_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*7 + 3, v___x_3255_);
v___x_3338_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3339_ = lean_st_mk_ref(v___x_3338_);
v___x_3340_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3313_, v___x_3255_, v___x_3337_, v___x_3339_, v___y_3057_, v___y_3058_);
lean_dec_ref_known(v___x_3337_, 7);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3342_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = lean_st_ref_get(v___x_3339_);
lean_dec(v___x_3339_);
lean_dec(v___x_3342_);
v___y_3228_ = v___x_3255_;
v___y_3229_ = v___x_3321_;
v___y_3230_ = v___x_3308_;
v___y_3231_ = v_a_3253_;
v_a_3232_ = v_a_3341_;
goto v___jp_3227_;
}
else
{
lean_dec(v___x_3339_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3343_; 
v_a_3343_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3340_, 1);
v___y_3228_ = v___x_3255_;
v___y_3229_ = v___x_3321_;
v___y_3230_ = v___x_3308_;
v___y_3231_ = v_a_3253_;
v_a_3232_ = v_a_3343_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3344_; 
v_a_3344_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3340_, 1);
v___y_3240_ = v___x_3308_;
v___y_3241_ = v_a_3253_;
v_a_3242_ = v_a_3344_;
goto v___jp_3239_;
}
}
}
}
else
{
uint8_t v___x_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; uint64_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec(v_snd_3314_);
lean_dec_ref(v___f_3055_);
v___x_3345_ = 0;
v___x_3346_ = 1;
v___x_3347_ = 0;
v___x_3348_ = 2;
v___x_3349_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3349_, 0, v___x_3345_);
lean_ctor_set_uint8(v___x_3349_, 1, v___x_3345_);
lean_ctor_set_uint8(v___x_3349_, 2, v___x_3345_);
lean_ctor_set_uint8(v___x_3349_, 3, v___x_3345_);
lean_ctor_set_uint8(v___x_3349_, 4, v___x_3345_);
lean_ctor_set_uint8(v___x_3349_, 5, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 6, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 7, v___x_3345_);
lean_ctor_set_uint8(v___x_3349_, 8, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 9, v___x_3346_);
lean_ctor_set_uint8(v___x_3349_, 10, v___x_3347_);
lean_ctor_set_uint8(v___x_3349_, 11, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 12, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 13, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 14, v___x_3348_);
lean_ctor_set_uint8(v___x_3349_, 15, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 16, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 17, v___x_3255_);
lean_ctor_set_uint8(v___x_3349_, 18, v___x_3255_);
v___x_3350_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set_uint64(v___x_3351_, sizeof(void*)*1, v___x_3350_);
v___x_3352_ = lean_box(1);
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3355_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3357_, 0, v___x_3351_);
lean_ctor_set(v___x_3357_, 1, v___x_3352_);
lean_ctor_set(v___x_3357_, 2, v___x_3354_);
lean_ctor_set(v___x_3357_, 3, v___x_3355_);
lean_ctor_set(v___x_3357_, 4, v___x_3356_);
lean_ctor_set(v___x_3357_, 5, v___x_3353_);
lean_ctor_set(v___x_3357_, 6, v___x_3356_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*7, v___x_3345_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*7 + 1, v___x_3345_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*7 + 2, v___x_3345_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*7 + 3, v___x_3255_);
v___x_3358_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3359_ = lean_st_mk_ref(v___x_3358_);
v___x_3360_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3313_, v___x_3357_, v___x_3359_, v___y_3057_, v___y_3058_);
lean_dec_ref_known(v___x_3357_, 7);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = lean_st_ref_get(v___x_3359_);
lean_dec(v___x_3359_);
lean_dec(v___x_3362_);
v___y_3234_ = v___x_3255_;
v___y_3235_ = v___x_3308_;
v___y_3236_ = v_a_3253_;
v_a_3237_ = v_a_3361_;
goto v___jp_3233_;
}
else
{
lean_dec(v___x_3359_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3363_; 
v_a_3363_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3360_, 1);
v___y_3234_ = v___x_3255_;
v___y_3235_ = v___x_3308_;
v___y_3236_ = v_a_3253_;
v_a_3237_ = v_a_3363_;
goto v___jp_3233_;
}
else
{
lean_object* v_a_3364_; 
v_a_3364_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3360_, 1);
v___y_3240_ = v___x_3308_;
v___y_3241_ = v_a_3253_;
v_a_3242_ = v_a_3364_;
goto v___jp_3239_;
}
}
}
}
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec(v___x_3311_);
lean_dec(v_name_3056_);
v___x_3365_ = lean_box(0);
lean_inc(v___y_3058_);
lean_inc_ref(v___y_3057_);
v___x_3366_ = lean_apply_4(v___f_3055_, v___x_3365_, v___y_3057_, v___y_3058_, lean_box(0));
v___y_3245_ = v___x_3308_;
v___y_3246_ = v_a_3253_;
v___y_3247_ = v___x_3366_;
goto v___jp_3244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3474_, lean_object* v_name_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3474_, v_name_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
return v_res_3479_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3523_ = lean_unsigned_to_nat(3137104340u);
v___x_3524_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3525_ = l_Lean_Name_num___override(v___x_3524_, v___x_3523_);
return v___x_3525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3528_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3529_ = l_Lean_Name_str___override(v___x_3528_, v___x_3527_);
return v___x_3529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3532_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3533_ = l_Lean_Name_str___override(v___x_3532_, v___x_3531_);
return v___x_3533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = lean_unsigned_to_nat(2u);
v___x_3535_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3536_ = l_Lean_Name_num___override(v___x_3535_, v___x_3534_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3538_; lean_object* v___x_3539_; 
v___f_3538_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3539_ = l_Lean_registerReservedNameAction(v___f_3538_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v___x_3540_; uint8_t v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_dec_ref_known(v___x_3539_, 1);
v___x_3540_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3541_ = 0;
v___x_3542_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3543_ = l_Lean_registerTraceClass(v___x_3540_, v___x_3541_, v___x_3542_);
return v___x_3543_;
}
else
{
return v___x_3539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3547_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3552_, lean_object* v_x_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3552_, v_x_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
return v_res_3557_;
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
