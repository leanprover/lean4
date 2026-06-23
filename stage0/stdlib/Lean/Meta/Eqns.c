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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1125_, size_t v_x_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1125_) == 0)
{
lean_object* v_es_1128_; lean_object* v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; lean_object* v_j_1132_; lean_object* v___x_1133_; 
v_es_1128_ = lean_ctor_get(v_x_1125_, 0);
v___x_1129_ = lean_box(2);
v___x_1130_ = ((size_t)31ULL);
v___x_1131_ = lean_usize_land(v_x_1126_, v___x_1130_);
v_j_1132_ = lean_usize_to_nat(v___x_1131_);
v___x_1133_ = lean_array_get_borrowed(v___x_1129_, v_es_1128_, v_j_1132_);
lean_dec(v_j_1132_);
switch(lean_obj_tag(v___x_1133_))
{
case 0:
{
lean_object* v_key_1134_; lean_object* v_val_1135_; uint8_t v___x_1136_; 
v_key_1134_ = lean_ctor_get(v___x_1133_, 0);
v_val_1135_ = lean_ctor_get(v___x_1133_, 1);
v___x_1136_ = lean_name_eq(v_x_1127_, v_key_1134_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_box(0);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; 
lean_inc(v_val_1135_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_val_1135_);
return v___x_1138_;
}
}
case 1:
{
lean_object* v_node_1139_; size_t v___x_1140_; size_t v___x_1141_; 
v_node_1139_ = lean_ctor_get(v___x_1133_, 0);
v___x_1140_ = ((size_t)5ULL);
v___x_1141_ = lean_usize_shift_right(v_x_1126_, v___x_1140_);
v_x_1125_ = v_node_1139_;
v_x_1126_ = v___x_1141_;
goto _start;
}
default: 
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
}
}
else
{
lean_object* v_ks_1144_; lean_object* v_vs_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_ks_1144_ = lean_ctor_get(v_x_1125_, 0);
v_vs_1145_ = lean_ctor_get(v_x_1125_, 1);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1144_, v_vs_1145_, v___x_1146_, v_x_1127_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
size_t v_x_339__boxed_1151_; lean_object* v_res_1152_; 
v_x_339__boxed_1151_ = lean_unbox_usize(v_x_1149_);
lean_dec(v_x_1149_);
v_res_1152_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1148_, v_x_339__boxed_1151_, v_x_1150_);
lean_dec(v_x_1150_);
lean_dec_ref(v_x_1148_);
return v_res_1152_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1153_; uint64_t v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(1723u);
v___x_1154_ = lean_uint64_of_nat(v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
uint64_t v___y_1158_; 
if (lean_obj_tag(v_x_1156_) == 0)
{
uint64_t v___x_1161_; 
v___x_1161_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1158_ = v___x_1161_;
goto v___jp_1157_;
}
else
{
uint64_t v_hash_1162_; 
v_hash_1162_ = lean_ctor_get_uint64(v_x_1156_, sizeof(void*)*2);
v___y_1158_ = v_hash_1162_;
goto v___jp_1157_;
}
v___jp_1157_:
{
size_t v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_uint64_to_usize(v___y_1158_);
v___x_1160_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1155_, v___x_1159_, v_x_1156_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1163_, v_x_1164_);
lean_dec(v_x_1164_);
lean_dec_ref(v_x_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v_env_1170_; lean_object* v___x_1171_; lean_object* v_asyncMode_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1169_ = lean_st_ref_get(v_a_1167_);
v_env_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc_ref(v_env_1170_);
lean_dec(v___x_1169_);
v___x_1171_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1172_ = lean_ctor_get(v___x_1171_, 2);
v___x_1173_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1174_ = lean_box(0);
v___x_1175_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1173_, v___x_1171_, v_env_1170_, v_asyncMode_1172_, v___x_1174_);
v___x_1176_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1175_, v_thmName_1166_);
lean_dec(v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec(v_thmName_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1182_, v_a_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1187_, v_a_1188_, v_a_1189_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_thmName_1187_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1193_, v_x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1196_, v_x_1197_, v_x_1198_);
lean_dec(v_x_1198_);
lean_dec_ref(v_x_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1200_, lean_object* v_x_1201_, size_t v_x_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1201_, v_x_1202_, v_x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
size_t v_x_438__boxed_1209_; lean_object* v_res_1210_; 
v_x_438__boxed_1209_ = lean_unbox_usize(v_x_1207_);
lean_dec(v_x_1207_);
v_res_1210_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1205_, v_x_1206_, v_x_438__boxed_1209_, v_x_1208_);
lean_dec(v_x_1208_);
lean_dec_ref(v_x_1206_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1211_, lean_object* v_keys_1212_, lean_object* v_vals_1213_, lean_object* v_heq_1214_, lean_object* v_i_1215_, lean_object* v_k_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1212_, v_vals_1213_, v_i_1215_, v_k_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1218_, lean_object* v_keys_1219_, lean_object* v_vals_1220_, lean_object* v_heq_1221_, lean_object* v_i_1222_, lean_object* v_k_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1218_, v_keys_1219_, v_vals_1220_, v_heq_1221_, v_i_1222_, v_k_1223_);
lean_dec(v_k_1223_);
lean_dec_ref(v_vals_1220_);
lean_dec_ref(v_keys_1219_);
return v_res_1224_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1225_, lean_object* v_i_1226_, lean_object* v_k_1227_){
_start:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_array_get_size(v_keys_1225_);
v___x_1229_ = lean_nat_dec_lt(v_i_1226_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec(v_i_1226_);
return v___x_1229_;
}
else
{
lean_object* v_k_x27_1230_; uint8_t v___x_1231_; 
v_k_x27_1230_ = lean_array_fget_borrowed(v_keys_1225_, v_i_1226_);
v___x_1231_ = lean_name_eq(v_k_1227_, v_k_x27_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_add(v_i_1226_, v___x_1232_);
lean_dec(v_i_1226_);
v_i_1226_ = v___x_1233_;
goto _start;
}
else
{
lean_dec(v_i_1226_);
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1235_, lean_object* v_i_1236_, lean_object* v_k_1237_){
_start:
{
uint8_t v_res_1238_; lean_object* v_r_1239_; 
v_res_1238_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1235_, v_i_1236_, v_k_1237_);
lean_dec(v_k_1237_);
lean_dec_ref(v_keys_1235_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1240_, size_t v_x_1241_, lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
lean_object* v_es_1243_; lean_object* v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; lean_object* v_j_1247_; lean_object* v___x_1248_; 
v_es_1243_ = lean_ctor_get(v_x_1240_, 0);
v___x_1244_ = lean_box(2);
v___x_1245_ = ((size_t)31ULL);
v___x_1246_ = lean_usize_land(v_x_1241_, v___x_1245_);
v_j_1247_ = lean_usize_to_nat(v___x_1246_);
v___x_1248_ = lean_array_get_borrowed(v___x_1244_, v_es_1243_, v_j_1247_);
lean_dec(v_j_1247_);
switch(lean_obj_tag(v___x_1248_))
{
case 0:
{
lean_object* v_key_1249_; uint8_t v___x_1250_; 
v_key_1249_ = lean_ctor_get(v___x_1248_, 0);
v___x_1250_ = lean_name_eq(v_x_1242_, v_key_1249_);
return v___x_1250_;
}
case 1:
{
lean_object* v_node_1251_; size_t v___x_1252_; size_t v___x_1253_; 
v_node_1251_ = lean_ctor_get(v___x_1248_, 0);
v___x_1252_ = ((size_t)5ULL);
v___x_1253_ = lean_usize_shift_right(v_x_1241_, v___x_1252_);
v_x_1240_ = v_node_1251_;
v_x_1241_ = v___x_1253_;
goto _start;
}
default: 
{
uint8_t v___x_1255_; 
v___x_1255_ = 0;
return v___x_1255_;
}
}
}
else
{
lean_object* v_ks_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_ks_1256_ = lean_ctor_get(v_x_1240_, 0);
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1256_, v___x_1257_, v_x_1242_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
size_t v_x_325__boxed_1262_; uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_x_325__boxed_1262_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_res_1263_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1259_, v_x_325__boxed_1262_, v_x_1261_);
lean_dec(v_x_1261_);
lean_dec_ref(v_x_1259_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
uint64_t v___y_1268_; 
if (lean_obj_tag(v_x_1266_) == 0)
{
uint64_t v___x_1271_; 
v___x_1271_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1268_ = v___x_1271_;
goto v___jp_1267_;
}
else
{
uint64_t v_hash_1272_; 
v_hash_1272_ = lean_ctor_get_uint64(v_x_1266_, sizeof(void*)*2);
v___y_1268_ = v_hash_1272_;
goto v___jp_1267_;
}
v___jp_1267_:
{
size_t v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_uint64_to_usize(v___y_1268_);
v___x_1270_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1265_, v___x_1269_, v_x_1266_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1273_, v_x_1274_);
lean_dec(v_x_1274_);
lean_dec_ref(v_x_1273_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v_env_1281_; lean_object* v___x_1282_; lean_object* v_asyncMode_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1280_ = lean_st_ref_get(v_a_1278_);
v_env_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc_ref(v_env_1281_);
lean_dec(v___x_1280_);
v___x_1282_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1283_ = lean_ctor_get(v___x_1282_, 2);
v___x_1284_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1285_ = lean_box(0);
v___x_1286_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1284_, v___x_1282_, v_env_1281_, v_asyncMode_1283_, v___x_1285_);
v___x_1287_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1286_, v_thmName_1277_);
lean_dec(v___x_1286_);
v___x_1288_ = lean_box(v___x_1287_);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec(v_thmName_1290_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1294_, v_a_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Meta_isEqnThm(v_thmName_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_thmName_1299_);
return v_res_1303_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1305_, v_x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1308_, v_x_1309_, v_x_1310_);
lean_dec(v_x_1310_);
lean_dec_ref(v_x_1309_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1313_, lean_object* v_x_1314_, size_t v_x_1315_, lean_object* v_x_1316_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1314_, v_x_1315_, v_x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1318_, lean_object* v_x_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_){
_start:
{
size_t v_x_417__boxed_1322_; uint8_t v_res_1323_; lean_object* v_r_1324_; 
v_x_417__boxed_1322_ = lean_unbox_usize(v_x_1320_);
lean_dec(v_x_1320_);
v_res_1323_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1318_, v_x_1319_, v_x_417__boxed_1322_, v_x_1321_);
lean_dec(v_x_1321_);
lean_dec_ref(v_x_1319_);
v_r_1324_ = lean_box(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1325_, lean_object* v_keys_1326_, lean_object* v_vals_1327_, lean_object* v_heq_1328_, lean_object* v_i_1329_, lean_object* v_k_1330_){
_start:
{
uint8_t v___x_1331_; 
v___x_1331_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1326_, v_i_1329_, v_k_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1332_, lean_object* v_keys_1333_, lean_object* v_vals_1334_, lean_object* v_heq_1335_, lean_object* v_i_1336_, lean_object* v_k_1337_){
_start:
{
uint8_t v_res_1338_; lean_object* v_r_1339_; 
v_res_1338_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1332_, v_keys_1333_, v_vals_1334_, v_heq_1335_, v_i_1336_, v_k_1337_);
lean_dec(v_k_1337_);
lean_dec_ref(v_vals_1334_);
lean_dec_ref(v_keys_1333_);
v_r_1339_ = lean_box(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
lean_object* v_ks_1344_; lean_object* v_vs_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1369_; 
v_ks_1344_ = lean_ctor_get(v_x_1340_, 0);
v_vs_1345_ = lean_ctor_get(v_x_1340_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_x_1340_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1347_ = v_x_1340_;
v_isShared_1348_ = v_isSharedCheck_1369_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_vs_1345_);
lean_inc(v_ks_1344_);
lean_dec(v_x_1340_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1369_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = lean_array_get_size(v_ks_1344_);
v___x_1350_ = lean_nat_dec_lt(v_x_1341_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
lean_dec(v_x_1341_);
v___x_1351_ = lean_array_push(v_ks_1344_, v_x_1342_);
v___x_1352_ = lean_array_push(v_vs_1345_, v_x_1343_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1352_);
lean_ctor_set(v___x_1347_, 0, v___x_1351_);
v___x_1354_ = v___x_1347_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
lean_object* v_k_x27_1356_; uint8_t v___x_1357_; 
v_k_x27_1356_ = lean_array_fget_borrowed(v_ks_1344_, v_x_1341_);
v___x_1357_ = lean_name_eq(v_x_1342_, v_k_x27_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1359_; 
if (v_isShared_1348_ == 0)
{
v___x_1359_ = v___x_1347_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_ks_1344_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_vs_1345_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = lean_nat_add(v_x_1341_, v___x_1360_);
lean_dec(v_x_1341_);
v_x_1340_ = v___x_1359_;
v_x_1341_ = v___x_1361_;
goto _start;
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1364_ = lean_array_fset(v_ks_1344_, v_x_1341_, v_x_1342_);
v___x_1365_ = lean_array_fset(v_vs_1345_, v_x_1341_, v_x_1343_);
lean_dec(v_x_1341_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1365_);
lean_ctor_set(v___x_1347_, 0, v___x_1364_);
v___x_1367_ = v___x_1347_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1370_, lean_object* v_k_1371_, lean_object* v_v_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1370_, v___x_1373_, v_k_1371_, v_v_1372_);
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1376_, size_t v_x_1377_, size_t v_x_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v_es_1381_; size_t v___x_1382_; size_t v___x_1383_; lean_object* v_j_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_es_1381_ = lean_ctor_get(v_x_1376_, 0);
v___x_1382_ = ((size_t)31ULL);
v___x_1383_ = lean_usize_land(v_x_1377_, v___x_1382_);
v_j_1384_ = lean_usize_to_nat(v___x_1383_);
v___x_1385_ = lean_array_get_size(v_es_1381_);
v___x_1386_ = lean_nat_dec_lt(v_j_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_dec(v_j_1384_);
lean_dec(v_x_1380_);
lean_dec(v_x_1379_);
return v_x_1376_;
}
else
{
lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1425_; 
lean_inc_ref(v_es_1381_);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v_x_1376_, 0);
lean_dec(v_unused_1426_);
v___x_1388_ = v_x_1376_;
v_isShared_1389_ = v_isSharedCheck_1425_;
goto v_resetjp_1387_;
}
else
{
lean_dec(v_x_1376_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1425_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v_v_1390_; lean_object* v___x_1391_; lean_object* v_xs_x27_1392_; lean_object* v___y_1394_; 
v_v_1390_ = lean_array_fget(v_es_1381_, v_j_1384_);
v___x_1391_ = lean_box(0);
v_xs_x27_1392_ = lean_array_fset(v_es_1381_, v_j_1384_, v___x_1391_);
switch(lean_obj_tag(v_v_1390_))
{
case 0:
{
lean_object* v_key_1399_; lean_object* v_val_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1410_; 
v_key_1399_ = lean_ctor_get(v_v_1390_, 0);
v_val_1400_ = lean_ctor_get(v_v_1390_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_v_1390_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1402_ = v_v_1390_;
v_isShared_1403_ = v_isSharedCheck_1410_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_val_1400_);
lean_inc(v_key_1399_);
lean_dec(v_v_1390_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1410_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_name_eq(v_x_1379_, v_key_1399_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_del_object(v___x_1402_);
v___x_1405_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1399_, v_val_1400_, v_x_1379_, v_x_1380_);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
v___y_1394_ = v___x_1406_;
goto v___jp_1393_;
}
else
{
lean_object* v___x_1408_; 
lean_dec(v_val_1400_);
lean_dec(v_key_1399_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v_x_1380_);
lean_ctor_set(v___x_1402_, 0, v_x_1379_);
v___x_1408_ = v___x_1402_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_x_1379_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_x_1380_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
v___y_1394_ = v___x_1408_;
goto v___jp_1393_;
}
}
}
}
case 1:
{
lean_object* v_node_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1423_; 
v_node_1411_ = lean_ctor_get(v_v_1390_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_v_1390_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1413_ = v_v_1390_;
v_isShared_1414_ = v_isSharedCheck_1423_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_node_1411_);
lean_dec(v_v_1390_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1423_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
size_t v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1415_ = ((size_t)5ULL);
v___x_1416_ = lean_usize_shift_right(v_x_1377_, v___x_1415_);
v___x_1417_ = ((size_t)1ULL);
v___x_1418_ = lean_usize_add(v_x_1378_, v___x_1417_);
v___x_1419_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1411_, v___x_1416_, v___x_1418_, v_x_1379_, v_x_1380_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1419_);
v___x_1421_ = v___x_1413_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
v___y_1394_ = v___x_1421_;
goto v___jp_1393_;
}
}
}
default: 
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_x_1379_);
lean_ctor_set(v___x_1424_, 1, v_x_1380_);
v___y_1394_ = v___x_1424_;
goto v___jp_1393_;
}
}
v___jp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = lean_array_fset(v_xs_x27_1392_, v_j_1384_, v___y_1394_);
lean_dec(v_j_1384_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1395_);
v___x_1397_ = v___x_1388_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
else
{
lean_object* v_ks_1427_; lean_object* v_vs_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1448_; 
v_ks_1427_ = lean_ctor_get(v_x_1376_, 0);
v_vs_1428_ = lean_ctor_get(v_x_1376_, 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1430_ = v_x_1376_;
v_isShared_1431_ = v_isSharedCheck_1448_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_vs_1428_);
lean_inc(v_ks_1427_);
lean_dec(v_x_1376_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1448_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_ks_1427_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_vs_1428_);
v___x_1433_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v_newNode_1434_; uint8_t v___y_1436_; size_t v___x_1442_; uint8_t v___x_1443_; 
v_newNode_1434_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1433_, v_x_1379_, v_x_1380_);
v___x_1442_ = ((size_t)7ULL);
v___x_1443_ = lean_usize_dec_le(v___x_1442_, v_x_1378_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1434_);
v___x_1445_ = lean_unsigned_to_nat(4u);
v___x_1446_ = lean_nat_dec_lt(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
v___y_1436_ = v___x_1446_;
goto v___jp_1435_;
}
else
{
v___y_1436_ = v___x_1443_;
goto v___jp_1435_;
}
v___jp_1435_:
{
if (v___y_1436_ == 0)
{
lean_object* v_ks_1437_; lean_object* v_vs_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_ks_1437_ = lean_ctor_get(v_newNode_1434_, 0);
lean_inc_ref(v_ks_1437_);
v_vs_1438_ = lean_ctor_get(v_newNode_1434_, 1);
lean_inc_ref(v_vs_1438_);
lean_dec_ref(v_newNode_1434_);
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1441_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1378_, v_ks_1437_, v_vs_1438_, v___x_1439_, v___x_1440_);
lean_dec_ref(v_vs_1438_);
lean_dec_ref(v_ks_1437_);
return v___x_1441_;
}
else
{
return v_newNode_1434_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1449_, lean_object* v_keys_1450_, lean_object* v_vals_1451_, lean_object* v_i_1452_, lean_object* v_entries_1453_){
_start:
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = lean_array_get_size(v_keys_1450_);
v___x_1455_ = lean_nat_dec_lt(v_i_1452_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_dec(v_i_1452_);
return v_entries_1453_;
}
else
{
lean_object* v_k_1456_; lean_object* v_v_1457_; uint64_t v___y_1459_; 
v_k_1456_ = lean_array_fget_borrowed(v_keys_1450_, v_i_1452_);
v_v_1457_ = lean_array_fget_borrowed(v_vals_1451_, v_i_1452_);
if (lean_obj_tag(v_k_1456_) == 0)
{
uint64_t v___x_1470_; 
v___x_1470_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1459_ = v___x_1470_;
goto v___jp_1458_;
}
else
{
uint64_t v_hash_1471_; 
v_hash_1471_ = lean_ctor_get_uint64(v_k_1456_, sizeof(void*)*2);
v___y_1459_ = v_hash_1471_;
goto v___jp_1458_;
}
v___jp_1458_:
{
size_t v_h_1460_; size_t v___x_1461_; lean_object* v___x_1462_; size_t v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; size_t v_h_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_h_1460_ = lean_uint64_to_usize(v___y_1459_);
v___x_1461_ = ((size_t)5ULL);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_sub(v_depth_1449_, v___x_1463_);
v___x_1465_ = lean_usize_mul(v___x_1461_, v___x_1464_);
v_h_1466_ = lean_usize_shift_right(v_h_1460_, v___x_1465_);
v___x_1467_ = lean_nat_add(v_i_1452_, v___x_1462_);
lean_dec(v_i_1452_);
lean_inc(v_v_1457_);
lean_inc(v_k_1456_);
v___x_1468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1453_, v_h_1466_, v_depth_1449_, v_k_1456_, v_v_1457_);
v_i_1452_ = v___x_1467_;
v_entries_1453_ = v___x_1468_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1472_, lean_object* v_keys_1473_, lean_object* v_vals_1474_, lean_object* v_i_1475_, lean_object* v_entries_1476_){
_start:
{
size_t v_depth_boxed_1477_; lean_object* v_res_1478_; 
v_depth_boxed_1477_ = lean_unbox_usize(v_depth_1472_);
lean_dec(v_depth_1472_);
v_res_1478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1477_, v_keys_1473_, v_vals_1474_, v_i_1475_, v_entries_1476_);
lean_dec_ref(v_vals_1474_);
lean_dec_ref(v_keys_1473_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_){
_start:
{
size_t v_x_626__boxed_1484_; size_t v_x_627__boxed_1485_; lean_object* v_res_1486_; 
v_x_626__boxed_1484_ = lean_unbox_usize(v_x_1480_);
lean_dec(v_x_1480_);
v_x_627__boxed_1485_ = lean_unbox_usize(v_x_1481_);
lean_dec(v_x_1481_);
v_res_1486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1479_, v_x_626__boxed_1484_, v_x_627__boxed_1485_, v_x_1482_, v_x_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_){
_start:
{
uint64_t v___y_1491_; 
if (lean_obj_tag(v_x_1488_) == 0)
{
uint64_t v___x_1495_; 
v___x_1495_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1491_ = v___x_1495_;
goto v___jp_1490_;
}
else
{
uint64_t v_hash_1496_; 
v_hash_1496_ = lean_ctor_get_uint64(v_x_1488_, sizeof(void*)*2);
v___y_1491_ = v_hash_1496_;
goto v___jp_1490_;
}
v___jp_1490_:
{
size_t v___x_1492_; size_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_uint64_to_usize(v___y_1491_);
v___x_1493_ = ((size_t)1ULL);
v___x_1494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1487_, v___x_1492_, v___x_1493_, v_x_1488_, v_x_1489_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1497_, lean_object* v_as_1498_, size_t v_i_1499_, size_t v_stop_1500_, lean_object* v_b_1501_){
_start:
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_usize_dec_eq(v_i_1499_, v_stop_1500_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; 
v___x_1503_ = lean_array_uget_borrowed(v_as_1498_, v_i_1499_);
lean_inc(v_declName_1497_);
lean_inc(v___x_1503_);
v___x_1504_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1501_, v___x_1503_, v_declName_1497_);
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1499_, v___x_1505_);
v_i_1499_ = v___x_1506_;
v_b_1501_ = v___x_1504_;
goto _start;
}
else
{
lean_dec(v_declName_1497_);
return v_b_1501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1508_, lean_object* v_as_1509_, lean_object* v_i_1510_, lean_object* v_stop_1511_, lean_object* v_b_1512_){
_start:
{
size_t v_i_boxed_1513_; size_t v_stop_boxed_1514_; lean_object* v_res_1515_; 
v_i_boxed_1513_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_stop_boxed_1514_ = lean_unbox_usize(v_stop_1511_);
lean_dec(v_stop_1511_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1508_, v_as_1509_, v_i_boxed_1513_, v_stop_boxed_1514_, v_b_1512_);
lean_dec_ref(v_as_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1516_, lean_object* v_declName_1517_, lean_object* v_s_1518_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = lean_array_get_size(v_eqThms_1516_);
v___x_1521_ = lean_nat_dec_lt(v___x_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_dec(v_declName_1517_);
return v_s_1518_;
}
else
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_nat_dec_le(v___x_1520_, v___x_1520_);
if (v___x_1522_ == 0)
{
if (v___x_1521_ == 0)
{
lean_dec(v_declName_1517_);
return v_s_1518_;
}
else
{
size_t v___x_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = lean_usize_of_nat(v___x_1520_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1517_, v_eqThms_1516_, v___x_1523_, v___x_1524_, v_s_1518_);
return v___x_1525_;
}
}
else
{
size_t v___x_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = ((size_t)0ULL);
v___x_1527_ = lean_usize_of_nat(v___x_1520_);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1517_, v_eqThms_1516_, v___x_1526_, v___x_1527_, v_s_1518_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1529_, lean_object* v_declName_1530_, lean_object* v_s_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1529_, v_declName_1530_, v_s_1531_);
lean_dec_ref(v_eqThms_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1533_, lean_object* v_eqThms_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v_env_1538_; lean_object* v_nextMacroScope_1539_; lean_object* v_ngen_1540_; lean_object* v_auxDeclNGen_1541_; lean_object* v_traceState_1542_; lean_object* v_messages_1543_; lean_object* v_infoState_1544_; lean_object* v_snapshotTasks_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1561_; 
v___x_1537_ = lean_st_ref_take(v_a_1535_);
v_env_1538_ = lean_ctor_get(v___x_1537_, 0);
v_nextMacroScope_1539_ = lean_ctor_get(v___x_1537_, 1);
v_ngen_1540_ = lean_ctor_get(v___x_1537_, 2);
v_auxDeclNGen_1541_ = lean_ctor_get(v___x_1537_, 3);
v_traceState_1542_ = lean_ctor_get(v___x_1537_, 4);
v_messages_1543_ = lean_ctor_get(v___x_1537_, 6);
v_infoState_1544_ = lean_ctor_get(v___x_1537_, 7);
v_snapshotTasks_1545_ = lean_ctor_get(v___x_1537_, 8);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1537_, 5);
lean_dec(v_unused_1562_);
v___x_1547_ = v___x_1537_;
v_isShared_1548_ = v_isSharedCheck_1561_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_snapshotTasks_1545_);
lean_inc(v_infoState_1544_);
lean_inc(v_messages_1543_);
lean_inc(v_traceState_1542_);
lean_inc(v_auxDeclNGen_1541_);
lean_inc(v_ngen_1540_);
lean_inc(v_nextMacroScope_1539_);
lean_inc(v_env_1538_);
lean_dec(v___x_1537_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1561_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v_asyncMode_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1549_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1550_ = lean_ctor_get(v___x_1549_, 2);
v___f_1551_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1551_, 0, v_eqThms_1534_);
lean_closure_set(v___f_1551_, 1, v_declName_1533_);
v___x_1552_ = lean_box(0);
v___x_1553_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1549_, v_env_1538_, v___f_1551_, v_asyncMode_1550_, v___x_1552_);
v___x_1554_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 5, v___x_1554_);
lean_ctor_set(v___x_1547_, 0, v___x_1553_);
v___x_1556_ = v___x_1547_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_nextMacroScope_1539_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_ngen_1540_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v_auxDeclNGen_1541_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_traceState_1542_);
lean_ctor_set(v_reuseFailAlloc_1560_, 5, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1560_, 6, v_messages_1543_);
lean_ctor_set(v_reuseFailAlloc_1560_, 7, v_infoState_1544_);
lean_ctor_set(v_reuseFailAlloc_1560_, 8, v_snapshotTasks_1545_);
v___x_1556_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_st_ref_set(v_a_1535_, v___x_1556_);
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1563_, lean_object* v_eqThms_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1563_, v_eqThms_1564_, v_a_1565_);
lean_dec(v_a_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1568_, lean_object* v_eqThms_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1568_, v_eqThms_1569_, v_a_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1574_, lean_object* v_eqThms_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1574_, v_eqThms_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1581_, v_x_1582_, v_x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1585_, lean_object* v_x_1586_, size_t v_x_1587_, size_t v_x_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1586_, v_x_1587_, v_x_1588_, v_x_1589_, v_x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
size_t v_x_895__boxed_1598_; size_t v_x_896__boxed_1599_; lean_object* v_res_1600_; 
v_x_895__boxed_1598_ = lean_unbox_usize(v_x_1594_);
lean_dec(v_x_1594_);
v_x_896__boxed_1599_ = lean_unbox_usize(v_x_1595_);
lean_dec(v_x_1595_);
v_res_1600_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1592_, v_x_1593_, v_x_895__boxed_1598_, v_x_896__boxed_1599_, v_x_1596_, v_x_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1601_, lean_object* v_n_1602_, lean_object* v_k_1603_, lean_object* v_v_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1602_, v_k_1603_, v_v_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1606_, size_t v_depth_1607_, lean_object* v_keys_1608_, lean_object* v_vals_1609_, lean_object* v_heq_1610_, lean_object* v_i_1611_, lean_object* v_entries_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1607_, v_keys_1608_, v_vals_1609_, v_i_1611_, v_entries_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1614_, lean_object* v_depth_1615_, lean_object* v_keys_1616_, lean_object* v_vals_1617_, lean_object* v_heq_1618_, lean_object* v_i_1619_, lean_object* v_entries_1620_){
_start:
{
size_t v_depth_boxed_1621_; lean_object* v_res_1622_; 
v_depth_boxed_1621_ = lean_unbox_usize(v_depth_1615_);
lean_dec(v_depth_1615_);
v_res_1622_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1614_, v_depth_boxed_1621_, v_keys_1616_, v_vals_1617_, v_heq_1618_, v_i_1619_, v_entries_1620_);
lean_dec_ref(v_vals_1617_);
lean_dec_ref(v_keys_1616_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1624_, v_x_1625_, v_x_1626_, v_x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1629_, lean_object* v_env_1630_, lean_object* v_idx_1631_, lean_object* v_eqs_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_nextEq_1639_; uint8_t v___x_1640_; 
v___x_1634_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_idx_1631_, v___x_1635_);
lean_dec(v_idx_1631_);
lean_inc(v___x_1636_);
v___x_1637_ = l_Nat_reprFast(v___x_1636_);
v___x_1638_ = lean_string_append(v___x_1634_, v___x_1637_);
lean_dec_ref(v___x_1637_);
lean_inc(v_declName_1629_);
lean_inc_ref(v_env_1630_);
v_nextEq_1639_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1630_, v_declName_1629_, v___x_1638_);
v___x_1640_ = l_Lean_Environment_containsOnBranch(v_env_1630_, v_nextEq_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; 
lean_dec(v_nextEq_1639_);
lean_dec(v___x_1636_);
lean_dec_ref(v_env_1630_);
lean_dec(v_declName_1629_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v_eqs_1632_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_array_push(v_eqs_1632_, v_nextEq_1639_);
v_idx_1631_ = v___x_1636_;
v_eqs_1632_ = v___x_1642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1644_, lean_object* v_env_1645_, lean_object* v_idx_1646_, lean_object* v_eqs_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1644_, v_env_1645_, v_idx_1646_, v_eqs_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1650_, lean_object* v_env_1651_, lean_object* v_idx_1652_, lean_object* v_eqs_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1650_, v_env_1651_, v_idx_1652_, v_eqs_1653_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1660_, lean_object* v_env_1661_, lean_object* v_idx_1662_, lean_object* v_eqs_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1660_, v_env_1661_, v_idx_1662_, v_eqs_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1673_; lean_object* v_env_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; uint8_t v___x_1678_; 
v___x_1673_ = lean_st_ref_get(v_a_1671_);
v_env_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc_ref_n(v_env_1674_, 3);
lean_dec(v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1670_);
v___x_1676_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1674_, v_declName_1670_, v___x_1675_);
v___x_1677_ = 1;
lean_inc(v___x_1676_);
v___x_1678_ = l_Lean_Environment_contains(v_env_1674_, v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v___x_1676_);
lean_dec_ref(v_env_1674_);
lean_dec(v_declName_1670_);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_mk_empty_array_with_capacity(v___x_1681_);
v___x_1683_ = lean_array_push(v___x_1682_, v___x_1676_);
lean_inc(v_declName_1670_);
v___x_1684_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1670_, v_env_1674_, v___x_1681_, v___x_1683_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc_n(v_a_1685_, 2);
lean_dec_ref_known(v___x_1684_, 1);
v___x_1686_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1670_, v_a_1685_, v_a_1671_);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v___x_1686_, 0);
lean_dec(v_unused_1695_);
v___x_1688_ = v___x_1686_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_dec(v___x_1686_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_a_1685_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_declName_1670_);
v_a_1696_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1684_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1684_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1704_, v_a_1705_);
lean_dec(v_a_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1708_, v_a_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1722_, lean_object* v_localInsts_1723_, lean_object* v_x_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1722_, v_localInsts_1723_, v_x_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1730_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1730_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1747_, lean_object* v_localInsts_1748_, lean_object* v_x_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1747_, v_localInsts_1748_, v_x_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1756_, lean_object* v_lctx_1757_, lean_object* v_localInsts_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1757_, v_localInsts_1758_, v_x_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_lctx_1767_, lean_object* v_localInsts_1768_, lean_object* v_x_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1766_, v_lctx_1767_, v_localInsts_1768_, v_x_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1779_, lean_object* v_as_x27_1780_, lean_object* v_b_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
if (lean_obj_tag(v_as_x27_1780_) == 0)
{
lean_object* v___x_1787_; 
lean_dec(v_declName_1779_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_b_1781_);
return v___x_1787_;
}
else
{
lean_object* v_head_1788_; lean_object* v_tail_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v_b_1781_);
v_head_1788_ = lean_ctor_get(v_as_x27_1780_, 0);
v_tail_1789_ = lean_ctor_get(v_as_x27_1780_, 1);
lean_inc(v_head_1788_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v_declName_1779_);
v___x_1790_ = lean_apply_6(v_head_1788_, v_declName_1779_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, lean_box(0));
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = lean_box(0);
if (lean_obj_tag(v_a_1791_) == 1)
{
lean_object* v_val_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1803_; 
v_val_1793_ = lean_ctor_get(v_a_1791_, 0);
lean_inc(v_val_1793_);
v___x_1794_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1779_, v_val_1793_, v___y_1785_);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1803_ == 0)
{
lean_object* v_unused_1804_; 
v_unused_1804_ = lean_ctor_get(v___x_1794_, 0);
lean_dec(v_unused_1804_);
v___x_1796_ = v___x_1794_;
v_isShared_1797_ = v_isSharedCheck_1803_;
goto v_resetjp_1795_;
}
else
{
lean_dec(v___x_1794_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1803_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1798_, 0, v_a_1791_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1792_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1799_);
v___x_1801_ = v___x_1796_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
else
{
lean_object* v___x_1805_; 
lean_dec(v_a_1791_);
v___x_1805_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1780_ = v_tail_1789_;
v_b_1781_ = v___x_1805_;
goto _start;
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_declName_1779_);
v_a_1807_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1790_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1790_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1815_, lean_object* v_as_x27_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1815_, v_as_x27_1816_, v_b_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v_as_x27_1816_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
lean_inc(v_declName_1824_);
v___x_1830_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1868_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1868_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1868_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_unbox(v_a_1831_);
lean_dec(v_a_1831_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec(v_declName_1824_);
v___x_1836_ = lean_box(0);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1836_);
v___x_1838_ = v___x_1833_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v___x_1840_; 
lean_del_object(v___x_1833_);
lean_inc(v_declName_1824_);
v___x_1840_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1824_, v___y_1828_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
if (lean_obj_tag(v_a_1841_) == 1)
{
lean_dec_ref_known(v_a_1841_, 1);
lean_dec(v_declName_1824_);
return v___x_1840_;
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1843_ = lean_st_ref_get(v___x_1842_);
v___x_1844_ = lean_box(0);
v___x_1845_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1846_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1824_, v___x_1843_, v___x_1845_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___x_1843_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1859_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1859_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1859_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_fst_1851_; 
v_fst_1851_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_fst_1851_);
lean_dec(v_a_1847_);
if (lean_obj_tag(v_fst_1851_) == 0)
{
lean_object* v___x_1853_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1844_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1844_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
else
{
lean_object* v_val_1855_; lean_object* v___x_1857_; 
v_val_1855_ = lean_ctor_get(v_fst_1851_, 0);
lean_inc(v_val_1855_);
lean_dec_ref_known(v_fst_1851_, 1);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_val_1855_);
v___x_1857_ = v___x_1849_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_val_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1846_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1846_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
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
}
else
{
lean_dec(v_declName_1824_);
return v___x_1840_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_declName_1824_);
v_a_1869_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1830_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1830_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
return v_res_1883_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1884_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = lean_box(1);
v___x_1888_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1889_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1888_);
lean_ctor_set(v___x_1890_, 2, v___x_1887_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___f_1899_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1899_, 0, v_declName_1893_);
v___x_1900_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1901_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1902_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1900_, v___x_1901_, v___f_1899_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1910_, lean_object* v_as_1911_, lean_object* v_as_x27_1912_, lean_object* v_b_1913_, lean_object* v_a_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1910_, v_as_x27_1912_, v_b_1913_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1921_, lean_object* v_as_1922_, lean_object* v_as_x27_1923_, lean_object* v_b_1924_, lean_object* v_a_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1921_, v_as_1922_, v_as_x27_1923_, v_b_1924_, v_a_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v_as_x27_1923_);
lean_dec(v_as_1922_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1938_ = lean_unsigned_to_nat(32u);
v___x_1939_ = lean_mk_empty_array_with_capacity(v___x_1938_);
lean_dec_ref(v___x_1939_);
v___x_1940_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1941_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1932_);
v___x_1942_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1942_, 0, v_declName_1932_);
v___x_1943_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1943_, 0, lean_box(0));
lean_closure_set(v___x_1943_, 1, v_declName_1932_);
lean_closure_set(v___x_1943_, 2, v___x_1942_);
v___x_1944_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1940_, v___x_1941_, v___x_1943_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; lean_object* v_env_1959_; lean_object* v___x_1960_; lean_object* v_mctx_1961_; lean_object* v_lctx_1962_; lean_object* v_options_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1958_ = lean_st_ref_get(v___y_1956_);
v_env_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_ref(v_env_1959_);
lean_dec(v___x_1958_);
v___x_1960_ = lean_st_ref_get(v___y_1954_);
v_mctx_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc_ref(v_mctx_1961_);
lean_dec(v___x_1960_);
v_lctx_1962_ = lean_ctor_get(v___y_1953_, 2);
v_options_1963_ = lean_ctor_get(v___y_1955_, 2);
lean_inc_ref(v_options_1963_);
lean_inc_ref(v_lctx_1962_);
v___x_1964_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1964_, 0, v_env_1959_);
lean_ctor_set(v___x_1964_, 1, v_mctx_1961_);
lean_ctor_set(v___x_1964_, 2, v_lctx_1962_);
lean_ctor_set(v___x_1964_, 3, v_options_1963_);
v___x_1965_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
lean_ctor_set(v___x_1965_, 1, v_msgData_1952_);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1973_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1974_; double v___x_1975_; 
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_float_of_nat(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1979_, lean_object* v_msg_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_ref_1986_; lean_object* v___x_1987_; lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2032_; 
v_ref_1986_ = lean_ctor_get(v___y_1983_, 5);
v___x_1987_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_2032_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2032_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v_traceState_1993_; lean_object* v_env_1994_; lean_object* v_nextMacroScope_1995_; lean_object* v_ngen_1996_; lean_object* v_auxDeclNGen_1997_; lean_object* v_cache_1998_; lean_object* v_messages_1999_; lean_object* v_infoState_2000_; lean_object* v_snapshotTasks_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2031_; 
v___x_1992_ = lean_st_ref_take(v___y_1984_);
v_traceState_1993_ = lean_ctor_get(v___x_1992_, 4);
v_env_1994_ = lean_ctor_get(v___x_1992_, 0);
v_nextMacroScope_1995_ = lean_ctor_get(v___x_1992_, 1);
v_ngen_1996_ = lean_ctor_get(v___x_1992_, 2);
v_auxDeclNGen_1997_ = lean_ctor_get(v___x_1992_, 3);
v_cache_1998_ = lean_ctor_get(v___x_1992_, 5);
v_messages_1999_ = lean_ctor_get(v___x_1992_, 6);
v_infoState_2000_ = lean_ctor_get(v___x_1992_, 7);
v_snapshotTasks_2001_ = lean_ctor_get(v___x_1992_, 8);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2003_ = v___x_1992_;
v_isShared_2004_ = v_isSharedCheck_2031_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snapshotTasks_2001_);
lean_inc(v_infoState_2000_);
lean_inc(v_messages_1999_);
lean_inc(v_cache_1998_);
lean_inc(v_traceState_1993_);
lean_inc(v_auxDeclNGen_1997_);
lean_inc(v_ngen_1996_);
lean_inc(v_nextMacroScope_1995_);
lean_inc(v_env_1994_);
lean_dec(v___x_1992_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2031_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
uint64_t v_tid_2005_; lean_object* v_traces_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2030_; 
v_tid_2005_ = lean_ctor_get_uint64(v_traceState_1993_, sizeof(void*)*1);
v_traces_2006_ = lean_ctor_get(v_traceState_1993_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_traceState_1993_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2008_ = v_traceState_1993_;
v_isShared_2009_ = v_isSharedCheck_2030_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_traces_2006_);
lean_dec(v_traceState_1993_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2030_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; double v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_2012_ = 0;
v___x_2013_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_2014_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2014_, 0, v_cls_1979_);
lean_ctor_set(v___x_2014_, 1, v___x_2010_);
lean_ctor_set(v___x_2014_, 2, v___x_2013_);
lean_ctor_set_float(v___x_2014_, sizeof(void*)*3, v___x_2011_);
lean_ctor_set_float(v___x_2014_, sizeof(void*)*3 + 8, v___x_2011_);
lean_ctor_set_uint8(v___x_2014_, sizeof(void*)*3 + 16, v___x_2012_);
v___x_2015_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_2016_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v_a_1988_);
lean_ctor_set(v___x_2016_, 2, v___x_2015_);
lean_inc(v_ref_1986_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v_ref_1986_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = l_Lean_PersistentArray_push___redArg(v_traces_2006_, v___x_2017_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2018_);
v___x_2020_ = v___x_2008_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2018_);
lean_ctor_set_uint64(v_reuseFailAlloc_2029_, sizeof(void*)*1, v_tid_2005_);
v___x_2020_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v___x_2020_);
v___x_2022_ = v___x_2003_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_env_1994_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_nextMacroScope_1995_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_ngen_1996_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v_auxDeclNGen_1997_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 5, v_cache_1998_);
lean_ctor_set(v_reuseFailAlloc_2028_, 6, v_messages_1999_);
lean_ctor_set(v_reuseFailAlloc_2028_, 7, v_infoState_2000_);
lean_ctor_set(v_reuseFailAlloc_2028_, 8, v_snapshotTasks_2001_);
v___x_2022_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = lean_st_ref_set(v___y_1984_, v___x_2022_);
v___x_2024_ = lean_box(0);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2024_);
v___x_2026_ = v___x_1990_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2033_, lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2033_, v_msg_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2041_, lean_object* v_as_2042_, size_t v_sz_2043_, size_t v_i_2044_, lean_object* v_b_2045_){
_start:
{
lean_object* v_a_2048_; uint8_t v___x_2052_; 
v___x_2052_ = lean_usize_dec_lt(v_i_2044_, v_sz_2043_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_b_2045_);
return v___x_2053_;
}
else
{
lean_object* v_a_2054_; lean_object* v_defValue_2055_; uint8_t v___x_2056_; uint8_t v___y_2058_; 
v_a_2054_ = lean_array_uget(v_as_2042_, v_i_2044_);
v_defValue_2055_ = lean_ctor_get(v_a_2054_, 1);
v___x_2056_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2041_, v_a_2054_);
if (v___x_2056_ == 0)
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_unbox(v_defValue_2055_);
if (v___x_2070_ == 0)
{
v___y_2058_ = v___x_2052_;
goto v___jp_2057_;
}
else
{
v___y_2058_ = v___x_2056_;
goto v___jp_2057_;
}
}
else
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_unbox(v_defValue_2055_);
v___y_2058_ = v___x_2071_;
goto v___jp_2057_;
}
v___jp_2057_:
{
if (v___y_2058_ == 0)
{
lean_object* v_name_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2068_; 
v_name_2059_ = lean_ctor_get(v_a_2054_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_a_2054_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v_a_2054_, 1);
lean_dec(v_unused_2069_);
v___x_2061_ = v_a_2054_;
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_name_2059_);
lean_dec(v_a_2054_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2063_, 0, v___x_2056_);
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
v___x_2066_ = lean_array_push(v_b_2045_, v___x_2065_);
v_a_2048_ = v___x_2066_;
goto v___jp_2047_;
}
}
}
else
{
lean_dec(v_a_2054_);
v_a_2048_ = v_b_2045_;
goto v___jp_2047_;
}
}
}
v___jp_2047_:
{
size_t v___x_2049_; size_t v___x_2050_; 
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2044_, v___x_2049_);
v_i_2044_ = v___x_2050_;
v_b_2045_ = v_a_2048_;
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
lean_object* v___x_2453_; lean_object* v_env_2454_; uint8_t v_isExporting_2455_; lean_object* v___x_2456_; lean_object* v_env_2457_; lean_object* v_nextMacroScope_2458_; lean_object* v_ngen_2459_; lean_object* v_auxDeclNGen_2460_; lean_object* v_traceState_2461_; lean_object* v_messages_2462_; lean_object* v_infoState_2463_; lean_object* v_snapshotTasks_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2518_; 
v___x_2453_ = lean_st_ref_get(v___y_2451_);
v_env_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_ref(v_env_2454_);
lean_dec(v___x_2453_);
v_isExporting_2455_ = lean_ctor_get_uint8(v_env_2454_, sizeof(void*)*8);
lean_dec_ref(v_env_2454_);
v___x_2456_ = lean_st_ref_take(v___y_2451_);
v_env_2457_ = lean_ctor_get(v___x_2456_, 0);
v_nextMacroScope_2458_ = lean_ctor_get(v___x_2456_, 1);
v_ngen_2459_ = lean_ctor_get(v___x_2456_, 2);
v_auxDeclNGen_2460_ = lean_ctor_get(v___x_2456_, 3);
v_traceState_2461_ = lean_ctor_get(v___x_2456_, 4);
v_messages_2462_ = lean_ctor_get(v___x_2456_, 6);
v_infoState_2463_ = lean_ctor_get(v___x_2456_, 7);
v_snapshotTasks_2464_ = lean_ctor_get(v___x_2456_, 8);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v___x_2456_, 5);
lean_dec(v_unused_2519_);
v___x_2466_ = v___x_2456_;
v_isShared_2467_ = v_isSharedCheck_2518_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_snapshotTasks_2464_);
lean_inc(v_infoState_2463_);
lean_inc(v_messages_2462_);
lean_inc(v_traceState_2461_);
lean_inc(v_auxDeclNGen_2460_);
lean_inc(v_ngen_2459_);
lean_inc(v_nextMacroScope_2458_);
lean_inc(v_env_2457_);
lean_dec(v___x_2456_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2518_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2468_ = l_Lean_Environment_setExporting(v_env_2457_, v_isExporting_2447_);
v___x_2469_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 5, v___x_2469_);
lean_ctor_set(v___x_2466_, 0, v___x_2468_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_nextMacroScope_2458_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_ngen_2459_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_auxDeclNGen_2460_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_traceState_2461_);
lean_ctor_set(v_reuseFailAlloc_2517_, 5, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2517_, 6, v_messages_2462_);
lean_ctor_set(v_reuseFailAlloc_2517_, 7, v_infoState_2463_);
lean_ctor_set(v_reuseFailAlloc_2517_, 8, v_snapshotTasks_2464_);
v___x_2471_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v_mctx_2474_; lean_object* v_zetaDeltaFVarIds_2475_; lean_object* v_postponed_2476_; lean_object* v_diag_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2515_; 
v___x_2472_ = lean_st_ref_set(v___y_2451_, v___x_2471_);
v___x_2473_ = lean_st_ref_take(v___y_2449_);
v_mctx_2474_ = lean_ctor_get(v___x_2473_, 0);
v_zetaDeltaFVarIds_2475_ = lean_ctor_get(v___x_2473_, 2);
v_postponed_2476_ = lean_ctor_get(v___x_2473_, 3);
v_diag_2477_ = lean_ctor_get(v___x_2473_, 4);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2515_ == 0)
{
lean_object* v_unused_2516_; 
v_unused_2516_ = lean_ctor_get(v___x_2473_, 1);
lean_dec(v_unused_2516_);
v___x_2479_ = v___x_2473_;
v_isShared_2480_ = v_isSharedCheck_2515_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_diag_2477_);
lean_inc(v_postponed_2476_);
lean_inc(v_zetaDeltaFVarIds_2475_);
lean_inc(v_mctx_2474_);
lean_dec(v___x_2473_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2515_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2481_);
v___x_2483_ = v___x_2479_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_mctx_2474_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_zetaDeltaFVarIds_2475_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_postponed_2476_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_diag_2477_);
v___x_2483_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; lean_object* v_r_2485_; 
v___x_2484_ = lean_st_ref_set(v___y_2449_, v___x_2483_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
v_r_2485_ = lean_apply_5(v_x_2446_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
if (lean_obj_tag(v_r_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2502_; 
v_a_2486_ = lean_ctor_get(v_r_2485_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_r_2485_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2488_ = v_r_2485_;
v_isShared_2489_ = v_isSharedCheck_2502_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v_r_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2502_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
lean_inc(v_a_2486_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 1);
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
v___x_2492_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2451_, v_isExporting_2455_, v___x_2469_, v___y_2449_, v___x_2481_, v___x_2491_);
lean_dec_ref(v___x_2491_);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; 
v_unused_2500_ = lean_ctor_get(v___x_2492_, 0);
lean_dec(v_unused_2500_);
v___x_2494_ = v___x_2492_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_dec(v___x_2492_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v_a_2486_);
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2486_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_a_2503_ = lean_ctor_get(v_r_2485_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v_r_2485_, 1);
v___x_2504_ = lean_box(0);
v___x_2505_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2451_, v_isExporting_2455_, v___x_2469_, v___y_2449_, v___x_2481_, v___x_2504_);
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
lean_ctor_set_tag(v___x_2507_, 1);
lean_ctor_set(v___x_2507_, 0, v_a_2503_);
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2503_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2520_, lean_object* v_isExporting_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
uint8_t v_isExporting_boxed_2527_; lean_object* v_res_2528_; 
v_isExporting_boxed_2527_ = lean_unbox(v_isExporting_2521_);
v_res_2528_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2520_, v_isExporting_boxed_2527_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2529_, uint8_t v_when_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
if (v_when_2530_ == 0)
{
lean_object* v___x_2536_; 
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
v___x_2536_ = lean_apply_5(v_x_2529_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, lean_box(0));
return v___x_2536_;
}
else
{
uint8_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = 0;
v___x_2538_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2529_, v___x_2537_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2539_, lean_object* v_when_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
uint8_t v_when_boxed_2546_; lean_object* v_res_2547_; 
v_when_boxed_2546_ = lean_unbox(v_when_2540_);
v_res_2547_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2539_, v_when_boxed_2546_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2547_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2550_ = l_Lean_stringToMessageData(v___x_2549_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2553_ = l_Lean_stringToMessageData(v___x_2552_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2556_ = l_Lean_stringToMessageData(v___x_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2557_, uint8_t v_nonRec_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v_env_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___f_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; 
v___x_2564_ = lean_st_ref_get(v___y_2562_);
v_env_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_ref(v_env_2565_);
lean_dec(v___x_2564_);
v___x_2566_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2557_);
v___x_2567_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2565_, v_declName_2557_, v___x_2566_);
v___x_2568_ = lean_box(v_nonRec_2558_);
lean_inc(v___x_2567_);
v___f_2569_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2569_, 0, v___x_2567_);
lean_closure_set(v___f_2569_, 1, v_declName_2557_);
lean_closure_set(v___f_2569_, 2, v___x_2568_);
lean_closure_set(v___f_2569_, 3, v___x_2566_);
v___x_2570_ = 1;
v___x_2571_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2569_, v___x_2570_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
if (lean_obj_tag(v_a_2572_) == 1)
{
lean_object* v_val_2573_; uint8_t v___x_2574_; 
v_val_2573_ = lean_ctor_get(v_a_2572_, 0);
lean_inc(v_val_2573_);
lean_dec_ref_known(v_a_2572_, 1);
v___x_2574_ = lean_name_eq(v_val_2573_, v___x_2567_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref_known(v___x_2571_, 1);
v___x_2575_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2576_ = l_Lean_MessageData_ofName(v_val_2573_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = l_Lean_MessageData_ofName(v___x_2567_);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2583_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
else
{
lean_dec(v_val_2573_);
lean_dec(v___x_2567_);
return v___x_2571_;
}
}
else
{
lean_dec(v_a_2572_);
lean_dec(v___x_2567_);
return v___x_2571_;
}
}
else
{
lean_dec(v___x_2567_);
return v___x_2571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2593_, lean_object* v_nonRec_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
uint8_t v_nonRec_boxed_2600_; lean_object* v_res_2601_; 
v_nonRec_boxed_2600_ = lean_unbox(v_nonRec_2594_);
v_res_2601_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2593_, v_nonRec_boxed_2600_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2602_, uint8_t v_nonRec_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v___x_2609_; lean_object* v___f_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2609_ = lean_box(v_nonRec_2603_);
v___f_2610_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2610_, 0, v_declName_2602_);
lean_closure_set(v___f_2610_, 1, v___x_2609_);
v___x_2611_ = lean_unsigned_to_nat(32u);
v___x_2612_ = lean_mk_empty_array_with_capacity(v___x_2611_);
lean_dec_ref(v___x_2612_);
v___x_2613_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2615_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2613_, v___x_2614_, v___f_2610_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2616_, lean_object* v_nonRec_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
uint8_t v_nonRec_boxed_2623_; lean_object* v_res_2624_; 
v_nonRec_boxed_2623_ = lean_unbox(v_nonRec_2617_);
v_res_2624_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2616_, v_nonRec_boxed_2623_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2625_, lean_object* v_as_2626_, lean_object* v_as_x27_2627_, lean_object* v_b_2628_, lean_object* v_a_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2625_, v_as_x27_2627_, v_b_2628_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2636_, lean_object* v_as_2637_, lean_object* v_as_x27_2638_, lean_object* v_b_2639_, lean_object* v_a_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2636_, v_as_2637_, v_as_x27_2638_, v_b_2639_, v_a_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v_as_x27_2638_);
lean_dec(v_as_2637_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2647_, lean_object* v_x_2648_, uint8_t v_isExporting_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2648_, v_isExporting_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2656_, lean_object* v_x_2657_, lean_object* v_isExporting_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
uint8_t v_isExporting_boxed_2664_; lean_object* v_res_2665_; 
v_isExporting_boxed_2664_ = lean_unbox(v_isExporting_2658_);
v_res_2665_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2656_, v_x_2657_, v_isExporting_boxed_2664_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2666_, lean_object* v_x_2667_, uint8_t v_when_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2667_, v_when_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2675_, lean_object* v_x_2676_, lean_object* v_when_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v_when_boxed_2683_; lean_object* v_res_2684_; 
v_when_boxed_2683_ = lean_unbox(v_when_2677_);
v_res_2684_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2675_, v_x_2676_, v_when_boxed_2683_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2685_, lean_object* v_msg_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2693_, v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
return v_res_2700_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_unsigned_to_nat(32u);
v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2704_ = ((size_t)5ULL);
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_unsigned_to_nat(32u);
v___x_2707_ = lean_mk_empty_array_with_capacity(v___x_2706_);
v___x_2708_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2709_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___x_2707_);
lean_ctor_set(v___x_2709_, 2, v___x_2705_);
lean_ctor_set(v___x_2709_, 3, v___x_2705_);
lean_ctor_set_usize(v___x_2709_, 4, v___x_2704_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; lean_object* v_traceState_2713_; lean_object* v_traces_2714_; lean_object* v___x_2715_; lean_object* v_traceState_2716_; lean_object* v_env_2717_; lean_object* v_nextMacroScope_2718_; lean_object* v_ngen_2719_; lean_object* v_auxDeclNGen_2720_; lean_object* v_cache_2721_; lean_object* v_messages_2722_; lean_object* v_infoState_2723_; lean_object* v_snapshotTasks_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2743_; 
v___x_2712_ = lean_st_ref_get(v___y_2710_);
v_traceState_2713_ = lean_ctor_get(v___x_2712_, 4);
lean_inc_ref(v_traceState_2713_);
lean_dec(v___x_2712_);
v_traces_2714_ = lean_ctor_get(v_traceState_2713_, 0);
lean_inc_ref(v_traces_2714_);
lean_dec_ref(v_traceState_2713_);
v___x_2715_ = lean_st_ref_take(v___y_2710_);
v_traceState_2716_ = lean_ctor_get(v___x_2715_, 4);
v_env_2717_ = lean_ctor_get(v___x_2715_, 0);
v_nextMacroScope_2718_ = lean_ctor_get(v___x_2715_, 1);
v_ngen_2719_ = lean_ctor_get(v___x_2715_, 2);
v_auxDeclNGen_2720_ = lean_ctor_get(v___x_2715_, 3);
v_cache_2721_ = lean_ctor_get(v___x_2715_, 5);
v_messages_2722_ = lean_ctor_get(v___x_2715_, 6);
v_infoState_2723_ = lean_ctor_get(v___x_2715_, 7);
v_snapshotTasks_2724_ = lean_ctor_get(v___x_2715_, 8);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2726_ = v___x_2715_;
v_isShared_2727_ = v_isSharedCheck_2743_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_snapshotTasks_2724_);
lean_inc(v_infoState_2723_);
lean_inc(v_messages_2722_);
lean_inc(v_cache_2721_);
lean_inc(v_traceState_2716_);
lean_inc(v_auxDeclNGen_2720_);
lean_inc(v_ngen_2719_);
lean_inc(v_nextMacroScope_2718_);
lean_inc(v_env_2717_);
lean_dec(v___x_2715_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2743_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
uint64_t v_tid_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2741_; 
v_tid_2728_ = lean_ctor_get_uint64(v_traceState_2716_, sizeof(void*)*1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_traceState_2716_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v_traceState_2716_, 0);
lean_dec(v_unused_2742_);
v___x_2730_ = v_traceState_2716_;
v_isShared_2731_ = v_isSharedCheck_2741_;
goto v_resetjp_2729_;
}
else
{
lean_dec(v_traceState_2716_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2741_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2732_);
lean_ctor_set_uint64(v_reuseFailAlloc_2740_, sizeof(void*)*1, v_tid_2728_);
v___x_2734_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2736_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 4, v___x_2734_);
v___x_2736_ = v___x_2726_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_env_2717_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_nextMacroScope_2718_);
lean_ctor_set(v_reuseFailAlloc_2739_, 2, v_ngen_2719_);
lean_ctor_set(v_reuseFailAlloc_2739_, 3, v_auxDeclNGen_2720_);
lean_ctor_set(v_reuseFailAlloc_2739_, 4, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2739_, 5, v_cache_2721_);
lean_ctor_set(v_reuseFailAlloc_2739_, 6, v_messages_2722_);
lean_ctor_set(v_reuseFailAlloc_2739_, 7, v_infoState_2723_);
lean_ctor_set(v_reuseFailAlloc_2739_, 8, v_snapshotTasks_2724_);
v___x_2736_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_st_ref_set(v___y_2710_, v___x_2736_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_traces_2714_);
return v___x_2738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2744_);
lean_dec(v___y_2744_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
uint8_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = 0;
v___x_2760_ = lean_box(v___x_2759_);
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
return v_res_2766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2775_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2776_ = l_Lean_MessageData_ofName(v_name_2770_);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2779_, lean_object* v_x_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2779_, v_x_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v_x_2780_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2785_){
_start:
{
if (lean_obj_tag(v_x_2785_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_a_2787_ = lean_ctor_get(v_x_2785_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_x_2785_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v_x_2785_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v_x_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 1);
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v_x_2785_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_x_2785_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v_x_2785_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v_x_2785_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 0);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2806_){
_start:
{
if (lean_obj_tag(v_e_2806_) == 0)
{
uint8_t v___x_2807_; 
v___x_2807_ = 2;
return v___x_2807_;
}
else
{
lean_object* v_a_2808_; uint8_t v___x_2809_; 
v_a_2808_ = lean_ctor_get(v_e_2806_, 0);
v___x_2809_ = lean_unbox(v_a_2808_);
if (v___x_2809_ == 0)
{
uint8_t v___x_2810_; 
v___x_2810_ = 1;
return v___x_2810_;
}
else
{
uint8_t v___x_2811_; 
v___x_2811_ = 0;
return v___x_2811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2812_){
_start:
{
uint8_t v_res_2813_; lean_object* v_r_2814_; 
v_res_2813_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2812_);
lean_dec_ref(v_e_2812_);
v_r_2814_ = lean_box(v_res_2813_);
return v_r_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2815_, size_t v_i_2816_, lean_object* v_bs_2817_){
_start:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_usize_dec_lt(v_i_2816_, v_sz_2815_);
if (v___x_2818_ == 0)
{
return v_bs_2817_;
}
else
{
lean_object* v_v_2819_; lean_object* v_msg_2820_; lean_object* v___x_2821_; lean_object* v_bs_x27_2822_; size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v_v_2819_ = lean_array_uget_borrowed(v_bs_2817_, v_i_2816_);
v_msg_2820_ = lean_ctor_get(v_v_2819_, 1);
lean_inc_ref(v_msg_2820_);
v___x_2821_ = lean_unsigned_to_nat(0u);
v_bs_x27_2822_ = lean_array_uset(v_bs_2817_, v_i_2816_, v___x_2821_);
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = lean_usize_add(v_i_2816_, v___x_2823_);
v___x_2825_ = lean_array_uset(v_bs_x27_2822_, v_i_2816_, v_msg_2820_);
v_i_2816_ = v___x_2824_;
v_bs_2817_ = v___x_2825_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2827_, lean_object* v_i_2828_, lean_object* v_bs_2829_){
_start:
{
size_t v_sz_boxed_2830_; size_t v_i_boxed_2831_; lean_object* v_res_2832_; 
v_sz_boxed_2830_ = lean_unbox_usize(v_sz_2827_);
lean_dec(v_sz_2827_);
v_i_boxed_2831_ = lean_unbox_usize(v_i_2828_);
lean_dec(v_i_2828_);
v_res_2832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2830_, v_i_boxed_2831_, v_bs_2829_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2833_, lean_object* v_data_2834_, lean_object* v_ref_2835_, lean_object* v_msg_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_fileName_2840_; lean_object* v_fileMap_2841_; lean_object* v_options_2842_; lean_object* v_currRecDepth_2843_; lean_object* v_maxRecDepth_2844_; lean_object* v_ref_2845_; lean_object* v_currNamespace_2846_; lean_object* v_openDecls_2847_; lean_object* v_initHeartbeats_2848_; lean_object* v_maxHeartbeats_2849_; lean_object* v_quotContext_2850_; lean_object* v_currMacroScope_2851_; uint8_t v_diag_2852_; lean_object* v_cancelTk_x3f_2853_; uint8_t v_suppressElabErrors_2854_; lean_object* v_inheritedTraceOptions_2855_; lean_object* v___x_2856_; lean_object* v_traceState_2857_; lean_object* v_traces_2858_; lean_object* v_ref_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; size_t v_sz_2862_; size_t v___x_2863_; lean_object* v___x_2864_; lean_object* v_msg_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2904_; 
v_fileName_2840_ = lean_ctor_get(v___y_2837_, 0);
v_fileMap_2841_ = lean_ctor_get(v___y_2837_, 1);
v_options_2842_ = lean_ctor_get(v___y_2837_, 2);
v_currRecDepth_2843_ = lean_ctor_get(v___y_2837_, 3);
v_maxRecDepth_2844_ = lean_ctor_get(v___y_2837_, 4);
v_ref_2845_ = lean_ctor_get(v___y_2837_, 5);
v_currNamespace_2846_ = lean_ctor_get(v___y_2837_, 6);
v_openDecls_2847_ = lean_ctor_get(v___y_2837_, 7);
v_initHeartbeats_2848_ = lean_ctor_get(v___y_2837_, 8);
v_maxHeartbeats_2849_ = lean_ctor_get(v___y_2837_, 9);
v_quotContext_2850_ = lean_ctor_get(v___y_2837_, 10);
v_currMacroScope_2851_ = lean_ctor_get(v___y_2837_, 11);
v_diag_2852_ = lean_ctor_get_uint8(v___y_2837_, sizeof(void*)*14);
v_cancelTk_x3f_2853_ = lean_ctor_get(v___y_2837_, 12);
v_suppressElabErrors_2854_ = lean_ctor_get_uint8(v___y_2837_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2855_ = lean_ctor_get(v___y_2837_, 13);
v___x_2856_ = lean_st_ref_get(v___y_2838_);
v_traceState_2857_ = lean_ctor_get(v___x_2856_, 4);
lean_inc_ref(v_traceState_2857_);
lean_dec(v___x_2856_);
v_traces_2858_ = lean_ctor_get(v_traceState_2857_, 0);
lean_inc_ref(v_traces_2858_);
lean_dec_ref(v_traceState_2857_);
v_ref_2859_ = l_Lean_replaceRef(v_ref_2835_, v_ref_2845_);
lean_inc_ref(v_inheritedTraceOptions_2855_);
lean_inc(v_cancelTk_x3f_2853_);
lean_inc(v_currMacroScope_2851_);
lean_inc(v_quotContext_2850_);
lean_inc(v_maxHeartbeats_2849_);
lean_inc(v_initHeartbeats_2848_);
lean_inc(v_openDecls_2847_);
lean_inc(v_currNamespace_2846_);
lean_inc(v_maxRecDepth_2844_);
lean_inc(v_currRecDepth_2843_);
lean_inc_ref(v_options_2842_);
lean_inc_ref(v_fileMap_2841_);
lean_inc_ref(v_fileName_2840_);
v___x_2860_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2860_, 0, v_fileName_2840_);
lean_ctor_set(v___x_2860_, 1, v_fileMap_2841_);
lean_ctor_set(v___x_2860_, 2, v_options_2842_);
lean_ctor_set(v___x_2860_, 3, v_currRecDepth_2843_);
lean_ctor_set(v___x_2860_, 4, v_maxRecDepth_2844_);
lean_ctor_set(v___x_2860_, 5, v_ref_2859_);
lean_ctor_set(v___x_2860_, 6, v_currNamespace_2846_);
lean_ctor_set(v___x_2860_, 7, v_openDecls_2847_);
lean_ctor_set(v___x_2860_, 8, v_initHeartbeats_2848_);
lean_ctor_set(v___x_2860_, 9, v_maxHeartbeats_2849_);
lean_ctor_set(v___x_2860_, 10, v_quotContext_2850_);
lean_ctor_set(v___x_2860_, 11, v_currMacroScope_2851_);
lean_ctor_set(v___x_2860_, 12, v_cancelTk_x3f_2853_);
lean_ctor_set(v___x_2860_, 13, v_inheritedTraceOptions_2855_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*14, v_diag_2852_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*14 + 1, v_suppressElabErrors_2854_);
v___x_2861_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2858_);
lean_dec_ref(v_traces_2858_);
v_sz_2862_ = lean_array_size(v___x_2861_);
v___x_2863_ = ((size_t)0ULL);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2862_, v___x_2863_, v___x_2861_);
v_msg_2865_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2865_, 0, v_data_2834_);
lean_ctor_set(v_msg_2865_, 1, v_msg_2836_);
lean_ctor_set(v_msg_2865_, 2, v___x_2864_);
v___x_2866_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2865_, v___x_2860_, v___y_2838_);
lean_dec_ref_known(v___x_2860_, 14);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2904_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2904_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v_traceState_2872_; lean_object* v_env_2873_; lean_object* v_nextMacroScope_2874_; lean_object* v_ngen_2875_; lean_object* v_auxDeclNGen_2876_; lean_object* v_cache_2877_; lean_object* v_messages_2878_; lean_object* v_infoState_2879_; lean_object* v_snapshotTasks_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2903_; 
v___x_2871_ = lean_st_ref_take(v___y_2838_);
v_traceState_2872_ = lean_ctor_get(v___x_2871_, 4);
v_env_2873_ = lean_ctor_get(v___x_2871_, 0);
v_nextMacroScope_2874_ = lean_ctor_get(v___x_2871_, 1);
v_ngen_2875_ = lean_ctor_get(v___x_2871_, 2);
v_auxDeclNGen_2876_ = lean_ctor_get(v___x_2871_, 3);
v_cache_2877_ = lean_ctor_get(v___x_2871_, 5);
v_messages_2878_ = lean_ctor_get(v___x_2871_, 6);
v_infoState_2879_ = lean_ctor_get(v___x_2871_, 7);
v_snapshotTasks_2880_ = lean_ctor_get(v___x_2871_, 8);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2882_ = v___x_2871_;
v_isShared_2883_ = v_isSharedCheck_2903_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_snapshotTasks_2880_);
lean_inc(v_infoState_2879_);
lean_inc(v_messages_2878_);
lean_inc(v_cache_2877_);
lean_inc(v_traceState_2872_);
lean_inc(v_auxDeclNGen_2876_);
lean_inc(v_ngen_2875_);
lean_inc(v_nextMacroScope_2874_);
lean_inc(v_env_2873_);
lean_dec(v___x_2871_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2903_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
uint64_t v_tid_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2901_; 
v_tid_2884_ = lean_ctor_get_uint64(v_traceState_2872_, sizeof(void*)*1);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_traceState_2872_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v_traceState_2872_, 0);
lean_dec(v_unused_2902_);
v___x_2886_ = v_traceState_2872_;
v_isShared_2887_ = v_isSharedCheck_2901_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v_traceState_2872_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2901_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v_ref_2835_);
lean_ctor_set(v___x_2888_, 1, v_a_2867_);
v___x_2889_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2833_, v___x_2888_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2889_);
v___x_2891_ = v___x_2886_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2889_);
lean_ctor_set_uint64(v_reuseFailAlloc_2900_, sizeof(void*)*1, v_tid_2884_);
v___x_2891_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2893_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 4, v___x_2891_);
v___x_2893_ = v___x_2882_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_env_2873_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_nextMacroScope_2874_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_ngen_2875_);
lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_auxDeclNGen_2876_);
lean_ctor_set(v_reuseFailAlloc_2899_, 4, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2899_, 5, v_cache_2877_);
lean_ctor_set(v_reuseFailAlloc_2899_, 6, v_messages_2878_);
lean_ctor_set(v_reuseFailAlloc_2899_, 7, v_infoState_2879_);
lean_ctor_set(v_reuseFailAlloc_2899_, 8, v_snapshotTasks_2880_);
v___x_2893_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2894_ = lean_st_ref_set(v___y_2838_, v___x_2893_);
v___x_2895_ = lean_box(0);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2895_);
v___x_2897_ = v___x_2869_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2905_, lean_object* v_data_2906_, lean_object* v_ref_2907_, lean_object* v_msg_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2905_, v_data_2906_, v_ref_2907_, v_msg_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2912_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2915_ = l_Lean_stringToMessageData(v___x_2914_);
return v___x_2915_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2916_; double v___x_2917_; 
v___x_2916_ = lean_unsigned_to_nat(1000u);
v___x_2917_ = lean_float_of_nat(v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2918_, uint8_t v_collapsed_2919_, lean_object* v_tag_2920_, lean_object* v_opts_2921_, uint8_t v_clsEnabled_2922_, lean_object* v_oldTraces_2923_, lean_object* v_msg_2924_, lean_object* v_resStartStop_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_fst_2929_; lean_object* v_snd_2930_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v_data_2934_; lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; lean_object* v___y_2950_; lean_object* v_a_2951_; uint8_t v___y_2966_; double v___y_2997_; 
v_fst_2929_ = lean_ctor_get(v_resStartStop_2925_, 0);
lean_inc(v_fst_2929_);
v_snd_2930_ = lean_ctor_get(v_resStartStop_2925_, 1);
lean_inc(v_snd_2930_);
lean_dec_ref(v_resStartStop_2925_);
v_fst_2945_ = lean_ctor_get(v_snd_2930_, 0);
lean_inc(v_fst_2945_);
v_snd_2946_ = lean_ctor_get(v_snd_2930_, 1);
lean_inc(v_snd_2946_);
lean_dec(v_snd_2930_);
v___x_2947_ = l_Lean_trace_profiler;
v___x_2948_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2921_, v___x_2947_);
if (v___x_2948_ == 0)
{
v___y_2966_ = v___x_2948_;
goto v___jp_2965_;
}
else
{
lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3003_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2921_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; double v___x_3006_; double v___x_3007_; double v___x_3008_; 
v___x_3004_ = l_Lean_trace_profiler_threshold;
v___x_3005_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2921_, v___x_3004_);
v___x_3006_ = lean_float_of_nat(v___x_3005_);
v___x_3007_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_3008_ = lean_float_div(v___x_3006_, v___x_3007_);
v___y_2997_ = v___x_3008_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; double v___x_3011_; 
v___x_3009_ = l_Lean_trace_profiler_threshold;
v___x_3010_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2921_, v___x_3009_);
v___x_3011_ = lean_float_of_nat(v___x_3010_);
v___y_2997_ = v___x_3011_;
goto v___jp_2996_;
}
}
v___jp_2931_:
{
lean_object* v___x_2935_; 
lean_inc(v___y_2933_);
v___x_2935_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2923_, v_data_2934_, v___y_2933_, v___y_2932_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v___x_2936_; 
lean_dec_ref_known(v___x_2935_, 1);
v___x_2936_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2929_);
return v___x_2936_;
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_fst_2929_);
v_a_2937_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2935_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2935_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
v___jp_2949_:
{
uint8_t v_result_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; double v___x_2955_; lean_object* v_data_2956_; 
v_result_2952_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2929_);
v___x_2953_ = lean_box(v_result_2952_);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
v___x_2955_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2920_);
lean_inc_ref(v___x_2954_);
lean_inc(v_cls_2918_);
v_data_2956_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2956_, 0, v_cls_2918_);
lean_ctor_set(v_data_2956_, 1, v___x_2954_);
lean_ctor_set(v_data_2956_, 2, v_tag_2920_);
lean_ctor_set_float(v_data_2956_, sizeof(void*)*3, v___x_2955_);
lean_ctor_set_float(v_data_2956_, sizeof(void*)*3 + 8, v___x_2955_);
lean_ctor_set_uint8(v_data_2956_, sizeof(void*)*3 + 16, v_collapsed_2919_);
if (v___x_2948_ == 0)
{
lean_dec_ref_known(v___x_2954_, 1);
lean_dec(v_snd_2946_);
lean_dec(v_fst_2945_);
lean_dec_ref(v_tag_2920_);
lean_dec(v_cls_2918_);
v___y_2932_ = v_a_2951_;
v___y_2933_ = v___y_2950_;
v_data_2934_ = v_data_2956_;
goto v___jp_2931_;
}
else
{
lean_object* v_data_2957_; double v___x_2958_; double v___x_2959_; 
lean_dec_ref_known(v_data_2956_, 3);
v_data_2957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2957_, 0, v_cls_2918_);
lean_ctor_set(v_data_2957_, 1, v___x_2954_);
lean_ctor_set(v_data_2957_, 2, v_tag_2920_);
v___x_2958_ = lean_unbox_float(v_fst_2945_);
lean_dec(v_fst_2945_);
lean_ctor_set_float(v_data_2957_, sizeof(void*)*3, v___x_2958_);
v___x_2959_ = lean_unbox_float(v_snd_2946_);
lean_dec(v_snd_2946_);
lean_ctor_set_float(v_data_2957_, sizeof(void*)*3 + 8, v___x_2959_);
lean_ctor_set_uint8(v_data_2957_, sizeof(void*)*3 + 16, v_collapsed_2919_);
v___y_2932_ = v_a_2951_;
v___y_2933_ = v___y_2950_;
v_data_2934_ = v_data_2957_;
goto v___jp_2931_;
}
}
v___jp_2960_:
{
lean_object* v_ref_2961_; lean_object* v___x_2962_; 
v_ref_2961_ = lean_ctor_get(v___y_2926_, 5);
lean_inc(v___y_2927_);
lean_inc_ref(v___y_2926_);
lean_inc(v_fst_2929_);
v___x_2962_ = lean_apply_4(v_msg_2924_, v_fst_2929_, v___y_2926_, v___y_2927_, lean_box(0));
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___y_2950_ = v_ref_2961_;
v_a_2951_ = v_a_2963_;
goto v___jp_2949_;
}
else
{
lean_object* v___x_2964_; 
lean_dec_ref_known(v___x_2962_, 1);
v___x_2964_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2950_ = v_ref_2961_;
v_a_2951_ = v___x_2964_;
goto v___jp_2949_;
}
}
v___jp_2965_:
{
if (v_clsEnabled_2922_ == 0)
{
if (v___y_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v_traceState_2968_; lean_object* v_env_2969_; lean_object* v_nextMacroScope_2970_; lean_object* v_ngen_2971_; lean_object* v_auxDeclNGen_2972_; lean_object* v_cache_2973_; lean_object* v_messages_2974_; lean_object* v_infoState_2975_; lean_object* v_snapshotTasks_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2995_; 
lean_dec(v_snd_2946_);
lean_dec(v_fst_2945_);
lean_dec_ref(v_msg_2924_);
lean_dec_ref(v_tag_2920_);
lean_dec(v_cls_2918_);
v___x_2967_ = lean_st_ref_take(v___y_2927_);
v_traceState_2968_ = lean_ctor_get(v___x_2967_, 4);
v_env_2969_ = lean_ctor_get(v___x_2967_, 0);
v_nextMacroScope_2970_ = lean_ctor_get(v___x_2967_, 1);
v_ngen_2971_ = lean_ctor_get(v___x_2967_, 2);
v_auxDeclNGen_2972_ = lean_ctor_get(v___x_2967_, 3);
v_cache_2973_ = lean_ctor_get(v___x_2967_, 5);
v_messages_2974_ = lean_ctor_get(v___x_2967_, 6);
v_infoState_2975_ = lean_ctor_get(v___x_2967_, 7);
v_snapshotTasks_2976_ = lean_ctor_get(v___x_2967_, 8);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2978_ = v___x_2967_;
v_isShared_2979_ = v_isSharedCheck_2995_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_snapshotTasks_2976_);
lean_inc(v_infoState_2975_);
lean_inc(v_messages_2974_);
lean_inc(v_cache_2973_);
lean_inc(v_traceState_2968_);
lean_inc(v_auxDeclNGen_2972_);
lean_inc(v_ngen_2971_);
lean_inc(v_nextMacroScope_2970_);
lean_inc(v_env_2969_);
lean_dec(v___x_2967_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2995_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
uint64_t v_tid_2980_; lean_object* v_traces_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2994_; 
v_tid_2980_ = lean_ctor_get_uint64(v_traceState_2968_, sizeof(void*)*1);
v_traces_2981_ = lean_ctor_get(v_traceState_2968_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_traceState_2968_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2983_ = v_traceState_2968_;
v_isShared_2984_ = v_isSharedCheck_2994_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_traces_2981_);
lean_dec(v_traceState_2968_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2994_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2923_, v_traces_2981_);
lean_dec_ref(v_traces_2981_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2985_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2985_);
lean_ctor_set_uint64(v_reuseFailAlloc_2993_, sizeof(void*)*1, v_tid_2980_);
v___x_2987_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2989_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 4, v___x_2987_);
v___x_2989_ = v___x_2978_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_env_2969_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_nextMacroScope_2970_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_ngen_2971_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_auxDeclNGen_2972_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2992_, 5, v_cache_2973_);
lean_ctor_set(v_reuseFailAlloc_2992_, 6, v_messages_2974_);
lean_ctor_set(v_reuseFailAlloc_2992_, 7, v_infoState_2975_);
lean_ctor_set(v_reuseFailAlloc_2992_, 8, v_snapshotTasks_2976_);
v___x_2989_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_st_ref_set(v___y_2927_, v___x_2989_);
v___x_2991_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2929_);
return v___x_2991_;
}
}
}
}
}
else
{
goto v___jp_2960_;
}
}
else
{
goto v___jp_2960_;
}
}
v___jp_2996_:
{
double v___x_2998_; double v___x_2999_; double v___x_3000_; uint8_t v___x_3001_; 
v___x_2998_ = lean_unbox_float(v_snd_2946_);
v___x_2999_ = lean_unbox_float(v_fst_2945_);
v___x_3000_ = lean_float_sub(v___x_2998_, v___x_2999_);
v___x_3001_ = lean_float_decLt(v___y_2997_, v___x_3000_);
v___y_2966_ = v___x_3001_;
goto v___jp_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_3012_, lean_object* v_collapsed_3013_, lean_object* v_tag_3014_, lean_object* v_opts_3015_, lean_object* v_clsEnabled_3016_, lean_object* v_oldTraces_3017_, lean_object* v_msg_3018_, lean_object* v_resStartStop_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
uint8_t v_collapsed_boxed_3023_; uint8_t v_clsEnabled_boxed_3024_; lean_object* v_res_3025_; 
v_collapsed_boxed_3023_ = lean_unbox(v_collapsed_3013_);
v_clsEnabled_boxed_3024_ = lean_unbox(v_clsEnabled_3016_);
v_res_3025_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_3012_, v_collapsed_boxed_3023_, v_tag_3014_, v_opts_3015_, v_clsEnabled_boxed_3024_, v_oldTraces_3017_, v_msg_3018_, v_resStartStop_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec_ref(v_opts_3015_);
return v_res_3025_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
lean_ctor_set(v___x_3030_, 2, v___x_3029_);
lean_ctor_set(v___x_3030_, 3, v___x_3029_);
lean_ctor_set(v___x_3030_, 4, v___x_3028_);
lean_ctor_set(v___x_3030_, 5, v___x_3028_);
lean_ctor_set(v___x_3030_, 6, v___x_3028_);
lean_ctor_set(v___x_3030_, 7, v___x_3028_);
lean_ctor_set(v___x_3030_, 8, v___x_3028_);
lean_ctor_set(v___x_3030_, 9, v___x_3028_);
return v___x_3030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3032_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
lean_ctor_set(v___x_3032_, 2, v___x_3031_);
lean_ctor_set(v___x_3032_, 3, v___x_3031_);
lean_ctor_set(v___x_3032_, 4, v___x_3031_);
lean_ctor_set(v___x_3032_, 5, v___x_3031_);
return v___x_3032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
lean_ctor_set(v___x_3034_, 2, v___x_3033_);
lean_ctor_set(v___x_3034_, 3, v___x_3033_);
lean_ctor_set(v___x_3034_, 4, v___x_3033_);
return v___x_3034_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3035_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3036_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3037_ = lean_box(1);
v___x_3038_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3039_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3038_);
lean_ctor_set(v___x_3040_, 2, v___x_3037_);
lean_ctor_set(v___x_3040_, 3, v___x_3036_);
lean_ctor_set(v___x_3040_, 4, v___x_3035_);
return v___x_3040_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3046_ = l_Lean_Name_append(v___x_3045_, v___x_3044_);
return v___x_3046_;
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
lean_object* v_val_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3158_; 
v_val_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3158_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_val_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3158_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_fst_3063_; lean_object* v_snd_3064_; lean_object* v___x_3065_; lean_object* v_env_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_fst_3063_ = lean_ctor_get(v_val_3059_, 0);
lean_inc_n(v_fst_3063_, 2);
v_snd_3064_ = lean_ctor_get(v_val_3059_, 1);
lean_inc_n(v_snd_3064_, 2);
lean_dec(v_val_3059_);
v___x_3065_ = lean_st_ref_get(v___y_3052_);
v_env_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc_ref(v_env_3066_);
lean_dec(v___x_3065_);
v___x_3067_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3066_, v_fst_3063_, v_snd_3064_);
v___x_3068_ = lean_name_eq(v_name_3050_, v___x_3067_);
lean_dec(v___x_3067_);
lean_dec(v_name_3050_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
lean_dec(v_snd_3064_);
lean_dec(v_fst_3063_);
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
v___x_3104_ = lean_box(v_hasTrace_3055_);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
return v___x_3105_;
}
else
{
uint8_t v___x_3106_; uint8_t v___x_3107_; uint8_t v___x_3108_; lean_object* v___x_3109_; uint64_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3106_ = 1;
v___x_3107_ = 0;
v___x_3108_ = 2;
v___x_3109_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3109_, 0, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3109_, 1, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3109_, 2, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3109_, 3, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3109_, 4, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3109_, 5, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 6, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 7, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3109_, 8, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 9, v___x_3106_);
lean_ctor_set_uint8(v___x_3109_, 10, v___x_3107_);
lean_ctor_set_uint8(v___x_3109_, 11, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 12, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 13, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 14, v___x_3108_);
lean_ctor_set_uint8(v___x_3109_, 15, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 16, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 17, v___x_3090_);
lean_ctor_set_uint8(v___x_3109_, 18, v___x_3090_);
v___x_3110_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3109_);
v___x_3111_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set_uint64(v___x_3111_, sizeof(void*)*1, v___x_3110_);
v___x_3112_ = lean_box(1);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3115_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3116_ = lean_box(0);
v___x_3117_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3117_, 0, v___x_3111_);
lean_ctor_set(v___x_3117_, 1, v___x_3112_);
lean_ctor_set(v___x_3117_, 2, v___x_3114_);
lean_ctor_set(v___x_3117_, 3, v___x_3115_);
lean_ctor_set(v___x_3117_, 4, v___x_3116_);
lean_ctor_set(v___x_3117_, 5, v___x_3113_);
lean_ctor_set(v___x_3117_, 6, v___x_3116_);
lean_ctor_set_uint8(v___x_3117_, sizeof(void*)*7, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3117_, sizeof(void*)*7 + 1, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3117_, sizeof(void*)*7 + 2, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3117_, sizeof(void*)*7 + 3, v___x_3068_);
v___x_3118_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3119_ = lean_st_mk_ref(v___x_3118_);
v___x_3120_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3063_, v___x_3068_, v___x_3117_, v___x_3119_, v___y_3051_, v___y_3052_);
lean_dec_ref_known(v___x_3117_, 7);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3122_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = lean_st_ref_get(v___x_3119_);
lean_dec(v___x_3119_);
lean_dec(v___x_3122_);
v_a_3092_ = v_a_3121_;
goto v___jp_3091_;
}
else
{
lean_dec(v___x_3119_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3123_; 
v_a_3123_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3120_, 1);
v_a_3092_ = v_a_3123_;
goto v___jp_3091_;
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
v_a_3124_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3120_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3120_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
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
uint8_t v___x_3132_; uint8_t v___x_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; uint64_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec(v_snd_3064_);
v___x_3132_ = 1;
v___x_3133_ = 0;
v___x_3134_ = 2;
v___x_3135_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3135_, 0, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3135_, 1, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3135_, 2, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3135_, 3, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3135_, 4, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3135_, 5, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 6, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 7, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3135_, 8, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 9, v___x_3132_);
lean_ctor_set_uint8(v___x_3135_, 10, v___x_3133_);
lean_ctor_set_uint8(v___x_3135_, 11, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 12, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 13, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 14, v___x_3134_);
lean_ctor_set_uint8(v___x_3135_, 15, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 16, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 17, v___x_3073_);
lean_ctor_set_uint8(v___x_3135_, 18, v___x_3073_);
v___x_3136_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3135_);
v___x_3137_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set_uint64(v___x_3137_, sizeof(void*)*1, v___x_3136_);
v___x_3138_ = lean_box(1);
v___x_3139_ = lean_unsigned_to_nat(0u);
v___x_3140_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3141_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3143_, 0, v___x_3137_);
lean_ctor_set(v___x_3143_, 1, v___x_3138_);
lean_ctor_set(v___x_3143_, 2, v___x_3140_);
lean_ctor_set(v___x_3143_, 3, v___x_3141_);
lean_ctor_set(v___x_3143_, 4, v___x_3142_);
lean_ctor_set(v___x_3143_, 5, v___x_3139_);
lean_ctor_set(v___x_3143_, 6, v___x_3142_);
lean_ctor_set_uint8(v___x_3143_, sizeof(void*)*7, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3143_, sizeof(void*)*7 + 1, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3143_, sizeof(void*)*7 + 2, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3143_, sizeof(void*)*7 + 3, v___x_3068_);
v___x_3144_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3145_ = lean_st_mk_ref(v___x_3144_);
v___x_3146_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3063_, v___x_3143_, v___x_3145_, v___y_3051_, v___y_3052_);
lean_dec_ref_known(v___x_3143_, 7);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3146_, 1);
v___x_3148_ = lean_st_ref_get(v___x_3145_);
lean_dec(v___x_3145_);
lean_dec(v___x_3148_);
v_a_3075_ = v_a_3147_;
goto v___jp_3074_;
}
else
{
lean_dec(v___x_3145_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3149_; 
v_a_3149_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3146_, 1);
v_a_3075_ = v_a_3149_;
goto v___jp_3074_;
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_del_object(v___x_3061_);
v_a_3150_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3146_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3146_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
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
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec(v___x_3058_);
lean_dec(v_name_3050_);
v___x_3159_ = lean_box(v_hasTrace_3055_);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3161_; lean_object* v___f_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v_a_3170_; lean_object* v___y_3183_; lean_object* v___y_3184_; uint8_t v_a_3185_; lean_object* v___y_3189_; uint8_t v___y_3190_; lean_object* v___y_3191_; lean_object* v_a_3192_; lean_object* v___y_3194_; uint8_t v___y_3195_; lean_object* v___y_3196_; lean_object* v_a_3197_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v_a_3201_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v_a_3206_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v_a_3218_; uint8_t v___y_3222_; uint8_t v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v_a_3226_; uint8_t v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v_a_3231_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_a_3236_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; 
v_inheritedTraceOptions_3161_ = lean_ctor_get(v___y_3051_, 13);
lean_inc(v_name_3050_);
v___f_3162_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3162_, 0, v_name_3050_);
v___x_3163_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3164_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3165_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3166_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3161_, v_options_3054_, v___x_3165_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3361_; uint8_t v___x_3362_; lean_object* v_a_3364_; lean_object* v_a_3377_; 
v___x_3361_ = l_Lean_trace_profiler;
v___x_3362_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3054_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3389_; lean_object* v_env_3390_; lean_object* v___x_3391_; 
lean_dec_ref(v___f_3162_);
lean_dec_ref(v___f_3049_);
v___x_3389_ = lean_st_ref_get(v___y_3052_);
v_env_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_ref(v_env_3390_);
lean_dec(v___x_3389_);
lean_inc(v_name_3050_);
v___x_3391_ = l_Lean_Meta_declFromEqLikeName(v_env_3390_, v_name_3050_);
if (lean_obj_tag(v___x_3391_) == 1)
{
lean_object* v_val_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3465_; 
v_val_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3465_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_val_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3465_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v_fst_3396_; lean_object* v_snd_3397_; lean_object* v___x_3398_; lean_object* v_env_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_fst_3396_ = lean_ctor_get(v_val_3392_, 0);
lean_inc_n(v_fst_3396_, 2);
v_snd_3397_ = lean_ctor_get(v_val_3392_, 1);
lean_inc_n(v_snd_3397_, 2);
lean_dec(v_val_3392_);
v___x_3398_ = lean_st_ref_get(v___y_3052_);
v_env_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc_ref(v_env_3399_);
lean_dec(v___x_3398_);
v___x_3400_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3399_, v_fst_3396_, v_snd_3397_);
v___x_3401_ = lean_name_eq(v_name_3050_, v___x_3400_);
lean_dec(v___x_3400_);
lean_dec(v_name_3050_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
lean_dec(v_snd_3397_);
lean_dec(v_fst_3396_);
v___x_3402_ = lean_box(v___x_3362_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3402_);
v___x_3404_ = v___x_3394_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
else
{
uint8_t v___x_3406_; 
lean_inc(v_snd_3397_);
v___x_3406_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3397_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3408_ = lean_string_dec_eq(v_snd_3397_, v___x_3407_);
lean_dec(v_snd_3397_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
lean_dec(v_fst_3396_);
v___x_3409_ = lean_box(v___x_3362_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3409_);
v___x_3411_ = v___x_3394_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
else
{
uint8_t v___x_3413_; uint8_t v___x_3414_; uint8_t v___x_3415_; lean_object* v___x_3416_; uint64_t v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_del_object(v___x_3394_);
v___x_3413_ = 1;
v___x_3414_ = 0;
v___x_3415_ = 2;
v___x_3416_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3416_, 0, v___x_3362_);
lean_ctor_set_uint8(v___x_3416_, 1, v___x_3362_);
lean_ctor_set_uint8(v___x_3416_, 2, v___x_3362_);
lean_ctor_set_uint8(v___x_3416_, 3, v___x_3362_);
lean_ctor_set_uint8(v___x_3416_, 4, v___x_3362_);
lean_ctor_set_uint8(v___x_3416_, 5, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 6, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 7, v___x_3362_);
lean_ctor_set_uint8(v___x_3416_, 8, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 9, v___x_3413_);
lean_ctor_set_uint8(v___x_3416_, 10, v___x_3414_);
lean_ctor_set_uint8(v___x_3416_, 11, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 12, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 13, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 14, v___x_3415_);
lean_ctor_set_uint8(v___x_3416_, 15, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 16, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 17, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3416_, 18, v_hasTrace_3055_);
v___x_3417_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3416_);
v___x_3418_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set_uint64(v___x_3418_, sizeof(void*)*1, v___x_3417_);
v___x_3419_ = lean_box(1);
v___x_3420_ = lean_unsigned_to_nat(0u);
v___x_3421_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3424_, 0, v___x_3418_);
lean_ctor_set(v___x_3424_, 1, v___x_3419_);
lean_ctor_set(v___x_3424_, 2, v___x_3421_);
lean_ctor_set(v___x_3424_, 3, v___x_3422_);
lean_ctor_set(v___x_3424_, 4, v___x_3423_);
lean_ctor_set(v___x_3424_, 5, v___x_3420_);
lean_ctor_set(v___x_3424_, 6, v___x_3423_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*7, v___x_3362_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*7 + 1, v___x_3362_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*7 + 2, v___x_3362_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*7 + 3, v_hasTrace_3055_);
v___x_3425_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3426_ = lean_st_mk_ref(v___x_3425_);
v___x_3427_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3396_, v_hasTrace_3055_, v___x_3424_, v___x_3426_, v___y_3051_, v___y_3052_);
lean_dec_ref_known(v___x_3424_, 7);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = lean_st_ref_get(v___x_3426_);
lean_dec(v___x_3426_);
lean_dec(v___x_3429_);
v_a_3377_ = v_a_3428_;
goto v___jp_3376_;
}
else
{
lean_dec(v___x_3426_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3430_; 
v_a_3430_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3427_, 1);
v_a_3377_ = v_a_3430_;
goto v___jp_3376_;
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
v_a_3431_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3427_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3427_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
}
else
{
uint8_t v___x_3439_; uint8_t v___x_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; uint64_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec(v_snd_3397_);
lean_del_object(v___x_3394_);
v___x_3439_ = 1;
v___x_3440_ = 0;
v___x_3441_ = 2;
v___x_3442_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3442_, 0, v___x_3362_);
lean_ctor_set_uint8(v___x_3442_, 1, v___x_3362_);
lean_ctor_set_uint8(v___x_3442_, 2, v___x_3362_);
lean_ctor_set_uint8(v___x_3442_, 3, v___x_3362_);
lean_ctor_set_uint8(v___x_3442_, 4, v___x_3362_);
lean_ctor_set_uint8(v___x_3442_, 5, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 6, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 7, v___x_3362_);
lean_ctor_set_uint8(v___x_3442_, 8, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 9, v___x_3439_);
lean_ctor_set_uint8(v___x_3442_, 10, v___x_3440_);
lean_ctor_set_uint8(v___x_3442_, 11, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 12, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 13, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 14, v___x_3441_);
lean_ctor_set_uint8(v___x_3442_, 15, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 16, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 17, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3442_, 18, v_hasTrace_3055_);
v___x_3443_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set_uint64(v___x_3444_, sizeof(void*)*1, v___x_3443_);
v___x_3445_ = lean_box(1);
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3449_ = lean_box(0);
v___x_3450_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3450_, 0, v___x_3444_);
lean_ctor_set(v___x_3450_, 1, v___x_3445_);
lean_ctor_set(v___x_3450_, 2, v___x_3447_);
lean_ctor_set(v___x_3450_, 3, v___x_3448_);
lean_ctor_set(v___x_3450_, 4, v___x_3449_);
lean_ctor_set(v___x_3450_, 5, v___x_3446_);
lean_ctor_set(v___x_3450_, 6, v___x_3449_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*7, v___x_3362_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*7 + 1, v___x_3362_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*7 + 2, v___x_3362_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*7 + 3, v_hasTrace_3055_);
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3452_ = lean_st_mk_ref(v___x_3451_);
v___x_3453_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3396_, v___x_3450_, v___x_3452_, v___y_3051_, v___y_3052_);
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
v_a_3364_ = v_a_3454_;
goto v___jp_3363_;
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
v_a_3364_ = v_a_3456_;
goto v___jp_3363_;
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
}
}
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec(v___x_3391_);
lean_dec(v_name_3050_);
v___x_3466_ = lean_box(v___x_3362_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
}
else
{
goto v___jp_3245_;
}
v___jp_3363_:
{
if (lean_obj_tag(v_a_3364_) == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = lean_box(v___x_3362_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
else
{
lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3374_; 
v_isSharedCheck_3374_ = !lean_is_exclusive(v_a_3364_);
if (v_isSharedCheck_3374_ == 0)
{
lean_object* v_unused_3375_; 
v_unused_3375_ = lean_ctor_get(v_a_3364_, 0);
lean_dec(v_unused_3375_);
v___x_3368_ = v_a_3364_;
v_isShared_3369_ = v_isSharedCheck_3374_;
goto v_resetjp_3367_;
}
else
{
lean_dec(v_a_3364_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3374_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_box(v_hasTrace_3055_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3370_);
v___x_3372_ = v___x_3368_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
v___jp_3376_:
{
if (lean_obj_tag(v_a_3377_) == 0)
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = lean_box(v___x_3362_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
else
{
lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3387_; 
v_isSharedCheck_3387_ = !lean_is_exclusive(v_a_3377_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v_a_3377_, 0);
lean_dec(v_unused_3388_);
v___x_3381_ = v_a_3377_;
v_isShared_3382_ = v_isSharedCheck_3387_;
goto v_resetjp_3380_;
}
else
{
lean_dec(v_a_3377_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3387_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = lean_box(v_hasTrace_3055_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set_tag(v___x_3381_, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3383_);
v___x_3385_ = v___x_3381_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
else
{
goto v___jp_3245_;
}
v___jp_3167_:
{
lean_object* v___x_3171_; double v___x_3172_; double v___x_3173_; double v___x_3174_; double v___x_3175_; double v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3171_ = lean_io_mono_nanos_now();
v___x_3172_ = lean_float_of_nat(v___y_3168_);
v___x_3173_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3174_ = lean_float_div(v___x_3172_, v___x_3173_);
v___x_3175_ = lean_float_of_nat(v___x_3171_);
v___x_3176_ = lean_float_div(v___x_3175_, v___x_3173_);
v___x_3177_ = lean_box_float(v___x_3174_);
v___x_3178_ = lean_box_float(v___x_3176_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v_a_3170_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3163_, v_hasTrace_3055_, v___x_3164_, v_options_3054_, v___x_3166_, v___y_3169_, v___f_3162_, v___x_3180_, v___y_3051_, v___y_3052_);
return v___x_3181_;
}
v___jp_3182_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_box(v_a_3185_);
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
v___y_3168_ = v___y_3183_;
v___y_3169_ = v___y_3184_;
v_a_3170_ = v___x_3187_;
goto v___jp_3167_;
}
v___jp_3188_:
{
if (lean_obj_tag(v_a_3192_) == 0)
{
v___y_3183_ = v___y_3189_;
v___y_3184_ = v___y_3191_;
v_a_3185_ = v___y_3190_;
goto v___jp_3182_;
}
else
{
lean_dec_ref_known(v_a_3192_, 1);
v___y_3183_ = v___y_3189_;
v___y_3184_ = v___y_3191_;
v_a_3185_ = v_hasTrace_3055_;
goto v___jp_3182_;
}
}
v___jp_3193_:
{
if (lean_obj_tag(v_a_3197_) == 0)
{
v___y_3183_ = v___y_3194_;
v___y_3184_ = v___y_3196_;
v_a_3185_ = v___y_3195_;
goto v___jp_3182_;
}
else
{
lean_dec_ref_known(v_a_3197_, 1);
v___y_3183_ = v___y_3194_;
v___y_3184_ = v___y_3196_;
v_a_3185_ = v_hasTrace_3055_;
goto v___jp_3182_;
}
}
v___jp_3198_:
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v_a_3201_);
v___y_3168_ = v___y_3199_;
v___y_3169_ = v___y_3200_;
v_a_3170_ = v___x_3202_;
goto v___jp_3167_;
}
v___jp_3203_:
{
lean_object* v___x_3207_; double v___x_3208_; double v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3207_ = lean_io_get_num_heartbeats();
v___x_3208_ = lean_float_of_nat(v___y_3204_);
v___x_3209_ = lean_float_of_nat(v___x_3207_);
v___x_3210_ = lean_box_float(v___x_3208_);
v___x_3211_ = lean_box_float(v___x_3209_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v_a_3206_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3163_, v_hasTrace_3055_, v___x_3164_, v_options_3054_, v___x_3166_, v___y_3205_, v___f_3162_, v___x_3213_, v___y_3051_, v___y_3052_);
return v___x_3214_;
}
v___jp_3215_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_box(v_a_3218_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
v___y_3204_ = v___y_3216_;
v___y_3205_ = v___y_3217_;
v_a_3206_ = v___x_3220_;
goto v___jp_3203_;
}
v___jp_3221_:
{
if (lean_obj_tag(v_a_3226_) == 0)
{
v___y_3216_ = v___y_3224_;
v___y_3217_ = v___y_3225_;
v_a_3218_ = v___y_3223_;
goto v___jp_3215_;
}
else
{
lean_dec_ref_known(v_a_3226_, 1);
v___y_3216_ = v___y_3224_;
v___y_3217_ = v___y_3225_;
v_a_3218_ = v___y_3222_;
goto v___jp_3215_;
}
}
v___jp_3227_:
{
if (lean_obj_tag(v_a_3231_) == 0)
{
uint8_t v___x_3232_; 
v___x_3232_ = 0;
v___y_3216_ = v___y_3229_;
v___y_3217_ = v___y_3230_;
v_a_3218_ = v___x_3232_;
goto v___jp_3215_;
}
else
{
lean_dec_ref_known(v_a_3231_, 1);
v___y_3216_ = v___y_3229_;
v___y_3217_ = v___y_3230_;
v_a_3218_ = v___y_3228_;
goto v___jp_3215_;
}
}
v___jp_3233_:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_a_3236_);
v___y_3204_ = v___y_3234_;
v___y_3205_ = v___y_3235_;
v_a_3206_ = v___x_3237_;
goto v___jp_3203_;
}
v___jp_3238_:
{
if (lean_obj_tag(v___y_3241_) == 0)
{
lean_object* v_a_3242_; uint8_t v___x_3243_; 
v_a_3242_ = lean_ctor_get(v___y_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___y_3241_, 1);
v___x_3243_ = lean_unbox(v_a_3242_);
lean_dec(v_a_3242_);
v___y_3216_ = v___y_3239_;
v___y_3217_ = v___y_3240_;
v_a_3218_ = v___x_3243_;
goto v___jp_3215_;
}
else
{
lean_object* v_a_3244_; 
v_a_3244_ = lean_ctor_get(v___y_3241_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___y_3241_, 1);
v___y_3234_ = v___y_3239_;
v___y_3235_ = v___y_3240_;
v_a_3236_ = v_a_3244_;
goto v___jp_3233_;
}
}
v___jp_3245_:
{
lean_object* v___x_3246_; lean_object* v_a_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3246_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3052_);
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref(v___x_3246_);
v___x_3248_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3249_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3054_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v_env_3252_; lean_object* v___x_3253_; 
lean_dec_ref(v___f_3049_);
v___x_3250_ = lean_io_mono_nanos_now();
v___x_3251_ = lean_st_ref_get(v___y_3052_);
v_env_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc_ref(v_env_3252_);
lean_dec(v___x_3251_);
lean_inc(v_name_3050_);
v___x_3253_ = l_Lean_Meta_declFromEqLikeName(v_env_3252_, v_name_3050_);
if (lean_obj_tag(v___x_3253_) == 1)
{
lean_object* v_val_3254_; lean_object* v_fst_3255_; lean_object* v_snd_3256_; lean_object* v___x_3257_; lean_object* v_env_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v_val_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_val_3254_);
lean_dec_ref_known(v___x_3253_, 1);
v_fst_3255_ = lean_ctor_get(v_val_3254_, 0);
lean_inc_n(v_fst_3255_, 2);
v_snd_3256_ = lean_ctor_get(v_val_3254_, 1);
lean_inc_n(v_snd_3256_, 2);
lean_dec(v_val_3254_);
v___x_3257_ = lean_st_ref_get(v___y_3052_);
v_env_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc_ref(v_env_3258_);
lean_dec(v___x_3257_);
v___x_3259_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3258_, v_fst_3255_, v_snd_3256_);
v___x_3260_ = lean_name_eq(v_name_3050_, v___x_3259_);
lean_dec(v___x_3259_);
lean_dec(v_name_3050_);
if (v___x_3260_ == 0)
{
lean_dec(v_snd_3256_);
lean_dec(v_fst_3255_);
v___y_3183_ = v___x_3250_;
v___y_3184_ = v_a_3247_;
v_a_3185_ = v___x_3249_;
goto v___jp_3182_;
}
else
{
uint8_t v___x_3261_; 
lean_inc(v_snd_3256_);
v___x_3261_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3256_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; uint8_t v___x_3263_; 
v___x_3262_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3263_ = lean_string_dec_eq(v_snd_3256_, v___x_3262_);
lean_dec(v_snd_3256_);
if (v___x_3263_ == 0)
{
lean_dec(v_fst_3255_);
v___y_3183_ = v___x_3250_;
v___y_3184_ = v_a_3247_;
v_a_3185_ = v___x_3249_;
goto v___jp_3182_;
}
else
{
uint8_t v___x_3264_; uint8_t v___x_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; uint64_t v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3264_ = 1;
v___x_3265_ = 0;
v___x_3266_ = 2;
v___x_3267_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3267_, 0, v___x_3249_);
lean_ctor_set_uint8(v___x_3267_, 1, v___x_3249_);
lean_ctor_set_uint8(v___x_3267_, 2, v___x_3249_);
lean_ctor_set_uint8(v___x_3267_, 3, v___x_3249_);
lean_ctor_set_uint8(v___x_3267_, 4, v___x_3249_);
lean_ctor_set_uint8(v___x_3267_, 5, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 6, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 7, v___x_3249_);
lean_ctor_set_uint8(v___x_3267_, 8, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 9, v___x_3264_);
lean_ctor_set_uint8(v___x_3267_, 10, v___x_3265_);
lean_ctor_set_uint8(v___x_3267_, 11, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 12, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 13, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 14, v___x_3266_);
lean_ctor_set_uint8(v___x_3267_, 15, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 16, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 17, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3267_, 18, v_hasTrace_3055_);
v___x_3268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set_uint64(v___x_3269_, sizeof(void*)*1, v___x_3268_);
v___x_3270_ = lean_box(1);
v___x_3271_ = lean_unsigned_to_nat(0u);
v___x_3272_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3273_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3275_, 0, v___x_3269_);
lean_ctor_set(v___x_3275_, 1, v___x_3270_);
lean_ctor_set(v___x_3275_, 2, v___x_3272_);
lean_ctor_set(v___x_3275_, 3, v___x_3273_);
lean_ctor_set(v___x_3275_, 4, v___x_3274_);
lean_ctor_set(v___x_3275_, 5, v___x_3271_);
lean_ctor_set(v___x_3275_, 6, v___x_3274_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*7, v___x_3249_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*7 + 1, v___x_3249_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*7 + 2, v___x_3249_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*7 + 3, v_hasTrace_3055_);
v___x_3276_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3277_ = lean_st_mk_ref(v___x_3276_);
v___x_3278_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3255_, v_hasTrace_3055_, v___x_3275_, v___x_3277_, v___y_3051_, v___y_3052_);
lean_dec_ref_known(v___x_3275_, 7);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3280_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3280_ = lean_st_ref_get(v___x_3277_);
lean_dec(v___x_3277_);
lean_dec(v___x_3280_);
v___y_3194_ = v___x_3250_;
v___y_3195_ = v___x_3249_;
v___y_3196_ = v_a_3247_;
v_a_3197_ = v_a_3279_;
goto v___jp_3193_;
}
else
{
lean_dec(v___x_3277_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3281_; 
v_a_3281_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3278_, 1);
v___y_3194_ = v___x_3250_;
v___y_3195_ = v___x_3249_;
v___y_3196_ = v_a_3247_;
v_a_3197_ = v_a_3281_;
goto v___jp_3193_;
}
else
{
lean_object* v_a_3282_; 
v_a_3282_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3278_, 1);
v___y_3199_ = v___x_3250_;
v___y_3200_ = v_a_3247_;
v_a_3201_ = v_a_3282_;
goto v___jp_3198_;
}
}
}
}
else
{
uint8_t v___x_3283_; uint8_t v___x_3284_; uint8_t v___x_3285_; lean_object* v___x_3286_; uint64_t v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_dec(v_snd_3256_);
v___x_3283_ = 1;
v___x_3284_ = 0;
v___x_3285_ = 2;
v___x_3286_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3286_, 0, v___x_3249_);
lean_ctor_set_uint8(v___x_3286_, 1, v___x_3249_);
lean_ctor_set_uint8(v___x_3286_, 2, v___x_3249_);
lean_ctor_set_uint8(v___x_3286_, 3, v___x_3249_);
lean_ctor_set_uint8(v___x_3286_, 4, v___x_3249_);
lean_ctor_set_uint8(v___x_3286_, 5, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 6, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 7, v___x_3249_);
lean_ctor_set_uint8(v___x_3286_, 8, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 9, v___x_3283_);
lean_ctor_set_uint8(v___x_3286_, 10, v___x_3284_);
lean_ctor_set_uint8(v___x_3286_, 11, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 12, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 13, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 14, v___x_3285_);
lean_ctor_set_uint8(v___x_3286_, 15, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 16, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 17, v_hasTrace_3055_);
lean_ctor_set_uint8(v___x_3286_, 18, v_hasTrace_3055_);
v___x_3287_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set_uint64(v___x_3288_, sizeof(void*)*1, v___x_3287_);
v___x_3289_ = lean_box(1);
v___x_3290_ = lean_unsigned_to_nat(0u);
v___x_3291_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3292_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3294_, 0, v___x_3288_);
lean_ctor_set(v___x_3294_, 1, v___x_3289_);
lean_ctor_set(v___x_3294_, 2, v___x_3291_);
lean_ctor_set(v___x_3294_, 3, v___x_3292_);
lean_ctor_set(v___x_3294_, 4, v___x_3293_);
lean_ctor_set(v___x_3294_, 5, v___x_3290_);
lean_ctor_set(v___x_3294_, 6, v___x_3293_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*7, v___x_3249_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*7 + 1, v___x_3249_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*7 + 2, v___x_3249_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*7 + 3, v_hasTrace_3055_);
v___x_3295_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3296_ = lean_st_mk_ref(v___x_3295_);
v___x_3297_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3255_, v___x_3294_, v___x_3296_, v___y_3051_, v___y_3052_);
lean_dec_ref_known(v___x_3294_, 7);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = lean_st_ref_get(v___x_3296_);
lean_dec(v___x_3296_);
lean_dec(v___x_3299_);
v___y_3189_ = v___x_3250_;
v___y_3190_ = v___x_3249_;
v___y_3191_ = v_a_3247_;
v_a_3192_ = v_a_3298_;
goto v___jp_3188_;
}
else
{
lean_dec(v___x_3296_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3300_; 
v_a_3300_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3297_, 1);
v___y_3189_ = v___x_3250_;
v___y_3190_ = v___x_3249_;
v___y_3191_ = v_a_3247_;
v_a_3192_ = v_a_3300_;
goto v___jp_3188_;
}
else
{
lean_object* v_a_3301_; 
v_a_3301_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3297_, 1);
v___y_3199_ = v___x_3250_;
v___y_3200_ = v_a_3247_;
v_a_3201_ = v_a_3301_;
goto v___jp_3198_;
}
}
}
}
}
else
{
lean_dec(v___x_3253_);
lean_dec(v_name_3050_);
v___y_3183_ = v___x_3250_;
v___y_3184_ = v_a_3247_;
v_a_3185_ = v___x_3249_;
goto v___jp_3182_;
}
}
else
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v_env_3304_; lean_object* v___x_3305_; 
v___x_3302_ = lean_io_get_num_heartbeats();
v___x_3303_ = lean_st_ref_get(v___y_3052_);
v_env_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc_ref(v_env_3304_);
lean_dec(v___x_3303_);
lean_inc(v_name_3050_);
v___x_3305_ = l_Lean_Meta_declFromEqLikeName(v_env_3304_, v_name_3050_);
if (lean_obj_tag(v___x_3305_) == 1)
{
lean_object* v_val_3306_; lean_object* v_fst_3307_; lean_object* v_snd_3308_; lean_object* v___x_3309_; lean_object* v_env_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v_val_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v_fst_3307_ = lean_ctor_get(v_val_3306_, 0);
lean_inc_n(v_fst_3307_, 2);
v_snd_3308_ = lean_ctor_get(v_val_3306_, 1);
lean_inc_n(v_snd_3308_, 2);
lean_dec(v_val_3306_);
v___x_3309_ = lean_st_ref_get(v___y_3052_);
v_env_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc_ref(v_env_3310_);
lean_dec(v___x_3309_);
v___x_3311_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3310_, v_fst_3307_, v_snd_3308_);
v___x_3312_ = lean_name_eq(v_name_3050_, v___x_3311_);
lean_dec(v___x_3311_);
lean_dec(v_name_3050_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
lean_dec(v_snd_3308_);
lean_dec(v_fst_3307_);
v___x_3313_ = lean_box(0);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3314_ = lean_apply_4(v___f_3049_, v___x_3313_, v___y_3051_, v___y_3052_, lean_box(0));
v___y_3239_ = v___x_3302_;
v___y_3240_ = v_a_3247_;
v___y_3241_ = v___x_3314_;
goto v___jp_3238_;
}
else
{
uint8_t v___x_3315_; 
lean_inc(v_snd_3308_);
v___x_3315_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3308_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3317_ = lean_string_dec_eq(v_snd_3308_, v___x_3316_);
lean_dec(v_snd_3308_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec(v_fst_3307_);
v___x_3318_ = lean_box(0);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3319_ = lean_apply_4(v___f_3049_, v___x_3318_, v___y_3051_, v___y_3052_, lean_box(0));
v___y_3239_ = v___x_3302_;
v___y_3240_ = v_a_3247_;
v___y_3241_ = v___x_3319_;
goto v___jp_3238_;
}
else
{
uint8_t v___x_3320_; uint8_t v___x_3321_; uint8_t v___x_3322_; lean_object* v___x_3323_; uint64_t v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec_ref(v___f_3049_);
v___x_3320_ = 1;
v___x_3321_ = 0;
v___x_3322_ = 2;
v___x_3323_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3323_, 0, v___x_3315_);
lean_ctor_set_uint8(v___x_3323_, 1, v___x_3315_);
lean_ctor_set_uint8(v___x_3323_, 2, v___x_3315_);
lean_ctor_set_uint8(v___x_3323_, 3, v___x_3315_);
lean_ctor_set_uint8(v___x_3323_, 4, v___x_3315_);
lean_ctor_set_uint8(v___x_3323_, 5, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 6, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 7, v___x_3315_);
lean_ctor_set_uint8(v___x_3323_, 8, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 9, v___x_3320_);
lean_ctor_set_uint8(v___x_3323_, 10, v___x_3321_);
lean_ctor_set_uint8(v___x_3323_, 11, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 12, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 13, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 14, v___x_3322_);
lean_ctor_set_uint8(v___x_3323_, 15, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 16, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 17, v___x_3249_);
lean_ctor_set_uint8(v___x_3323_, 18, v___x_3249_);
v___x_3324_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3323_);
v___x_3325_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set_uint64(v___x_3325_, sizeof(void*)*1, v___x_3324_);
v___x_3326_ = lean_box(1);
v___x_3327_ = lean_unsigned_to_nat(0u);
v___x_3328_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3329_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3331_, 0, v___x_3325_);
lean_ctor_set(v___x_3331_, 1, v___x_3326_);
lean_ctor_set(v___x_3331_, 2, v___x_3328_);
lean_ctor_set(v___x_3331_, 3, v___x_3329_);
lean_ctor_set(v___x_3331_, 4, v___x_3330_);
lean_ctor_set(v___x_3331_, 5, v___x_3327_);
lean_ctor_set(v___x_3331_, 6, v___x_3330_);
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*7, v___x_3315_);
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*7 + 1, v___x_3315_);
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*7 + 2, v___x_3315_);
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*7 + 3, v___x_3249_);
v___x_3332_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3333_ = lean_st_mk_ref(v___x_3332_);
v___x_3334_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3307_, v___x_3249_, v___x_3331_, v___x_3333_, v___y_3051_, v___y_3052_);
lean_dec_ref_known(v___x_3331_, 7);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
v___x_3336_ = lean_st_ref_get(v___x_3333_);
lean_dec(v___x_3333_);
lean_dec(v___x_3336_);
v___y_3222_ = v___x_3249_;
v___y_3223_ = v___x_3315_;
v___y_3224_ = v___x_3302_;
v___y_3225_ = v_a_3247_;
v_a_3226_ = v_a_3335_;
goto v___jp_3221_;
}
else
{
lean_dec(v___x_3333_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3337_; 
v_a_3337_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3337_);
lean_dec_ref_known(v___x_3334_, 1);
v___y_3222_ = v___x_3249_;
v___y_3223_ = v___x_3315_;
v___y_3224_ = v___x_3302_;
v___y_3225_ = v_a_3247_;
v_a_3226_ = v_a_3337_;
goto v___jp_3221_;
}
else
{
lean_object* v_a_3338_; 
v_a_3338_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3334_, 1);
v___y_3234_ = v___x_3302_;
v___y_3235_ = v_a_3247_;
v_a_3236_ = v_a_3338_;
goto v___jp_3233_;
}
}
}
}
else
{
uint8_t v___x_3339_; uint8_t v___x_3340_; uint8_t v___x_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; uint64_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_dec(v_snd_3308_);
lean_dec_ref(v___f_3049_);
v___x_3339_ = 0;
v___x_3340_ = 1;
v___x_3341_ = 0;
v___x_3342_ = 2;
v___x_3343_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3343_, 0, v___x_3339_);
lean_ctor_set_uint8(v___x_3343_, 1, v___x_3339_);
lean_ctor_set_uint8(v___x_3343_, 2, v___x_3339_);
lean_ctor_set_uint8(v___x_3343_, 3, v___x_3339_);
lean_ctor_set_uint8(v___x_3343_, 4, v___x_3339_);
lean_ctor_set_uint8(v___x_3343_, 5, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 6, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 7, v___x_3339_);
lean_ctor_set_uint8(v___x_3343_, 8, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 9, v___x_3340_);
lean_ctor_set_uint8(v___x_3343_, 10, v___x_3341_);
lean_ctor_set_uint8(v___x_3343_, 11, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 12, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 13, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 14, v___x_3342_);
lean_ctor_set_uint8(v___x_3343_, 15, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 16, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 17, v___x_3249_);
lean_ctor_set_uint8(v___x_3343_, 18, v___x_3249_);
v___x_3344_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3343_);
v___x_3345_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set_uint64(v___x_3345_, sizeof(void*)*1, v___x_3344_);
v___x_3346_ = lean_box(1);
v___x_3347_ = lean_unsigned_to_nat(0u);
v___x_3348_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3349_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3351_, 0, v___x_3345_);
lean_ctor_set(v___x_3351_, 1, v___x_3346_);
lean_ctor_set(v___x_3351_, 2, v___x_3348_);
lean_ctor_set(v___x_3351_, 3, v___x_3349_);
lean_ctor_set(v___x_3351_, 4, v___x_3350_);
lean_ctor_set(v___x_3351_, 5, v___x_3347_);
lean_ctor_set(v___x_3351_, 6, v___x_3350_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*7, v___x_3339_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*7 + 1, v___x_3339_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*7 + 2, v___x_3339_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*7 + 3, v___x_3249_);
v___x_3352_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3353_ = lean_st_mk_ref(v___x_3352_);
v___x_3354_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3307_, v___x_3351_, v___x_3353_, v___y_3051_, v___y_3052_);
lean_dec_ref_known(v___x_3351_, 7);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = lean_st_ref_get(v___x_3353_);
lean_dec(v___x_3353_);
lean_dec(v___x_3356_);
v___y_3228_ = v___x_3249_;
v___y_3229_ = v___x_3302_;
v___y_3230_ = v_a_3247_;
v_a_3231_ = v_a_3355_;
goto v___jp_3227_;
}
else
{
lean_dec(v___x_3353_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3357_; 
v_a_3357_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3354_, 1);
v___y_3228_ = v___x_3249_;
v___y_3229_ = v___x_3302_;
v___y_3230_ = v_a_3247_;
v_a_3231_ = v_a_3357_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3358_; 
v_a_3358_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3354_, 1);
v___y_3234_ = v___x_3302_;
v___y_3235_ = v_a_3247_;
v_a_3236_ = v_a_3358_;
goto v___jp_3233_;
}
}
}
}
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec(v___x_3305_);
lean_dec(v_name_3050_);
v___x_3359_ = lean_box(0);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3360_ = lean_apply_4(v___f_3049_, v___x_3359_, v___y_3051_, v___y_3052_, lean_box(0));
v___y_3239_ = v___x_3302_;
v___y_3240_ = v_a_3247_;
v___y_3241_ = v___x_3360_;
goto v___jp_3238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3468_, lean_object* v_name_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3468_, v_name_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3517_ = lean_unsigned_to_nat(3137104340u);
v___x_3518_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3519_ = l_Lean_Name_num___override(v___x_3518_, v___x_3517_);
return v___x_3519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3522_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3523_ = l_Lean_Name_str___override(v___x_3522_, v___x_3521_);
return v___x_3523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3526_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3527_ = l_Lean_Name_str___override(v___x_3526_, v___x_3525_);
return v___x_3527_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_unsigned_to_nat(2u);
v___x_3529_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3530_ = l_Lean_Name_num___override(v___x_3529_, v___x_3528_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3532_; lean_object* v___x_3533_; 
v___f_3532_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3533_ = l_Lean_registerReservedNameAction(v___f_3532_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3534_; uint8_t v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec_ref_known(v___x_3533_, 1);
v___x_3534_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3535_ = 0;
v___x_3536_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3537_ = l_Lean_registerTraceClass(v___x_3534_, v___x_3535_, v___x_3536_);
return v___x_3537_;
}
else
{
return v___x_3533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3540_, lean_object* v_x_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3541_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3546_, v_x_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
return v_res_3551_;
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
