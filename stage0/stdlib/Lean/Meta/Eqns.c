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
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
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
uint8_t l_Lean_initializing();
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*);
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
v___x_243_ = l_Lean_Meta_isMatcherCore(v_env_226_, v_head_229_);
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
uint8_t v___x_450_; 
v___x_450_ = l_Lean_initializing();
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec_ref(v_f_448_);
v___x_451_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_453_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_454_ = lean_st_ref_take(v___x_453_);
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v_f_448_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_st_ref_set(v___x_453_, v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Meta_registerGetEqnsFn(v_f_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_471_; lean_object* v_env_472_; uint8_t v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_st_ref_get(v_a_465_);
v_env_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc_ref(v_env_472_);
lean_dec(v___x_471_);
v___x_473_ = 0;
lean_inc(v_declName_461_);
v___x_474_ = l_Lean_Environment_findAsync_x3f(v_env_472_, v_declName_461_, v___x_473_);
if (lean_obj_tag(v___x_474_) == 1)
{
lean_object* v_val_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_506_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_506_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_506_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_val_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_506_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
uint8_t v_kind_479_; 
v_kind_479_ = lean_ctor_get_uint8(v_val_475_, sizeof(void*)*3);
if (v_kind_479_ == 0)
{
lean_object* v_sig_480_; lean_object* v___x_481_; lean_object* v_env_482_; uint8_t v___x_483_; 
v_sig_480_ = lean_ctor_get(v_val_475_, 1);
lean_inc_ref(v_sig_480_);
lean_dec(v_val_475_);
v___x_481_ = lean_st_ref_get(v_a_465_);
v_env_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref(v_env_482_);
lean_dec(v___x_481_);
v___x_483_ = l_Lean_Meta_isMatcherCore(v_env_482_, v_declName_461_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v_type_485_; lean_object* v___x_486_; 
lean_del_object(v___x_477_);
v___x_484_ = lean_task_get_own(v_sig_480_);
v_type_485_ = lean_ctor_get(v___x_484_, 2);
lean_inc_ref(v_type_485_);
lean_dec(v___x_484_);
v___x_486_ = l_Lean_Meta_isProp(v_type_485_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_501_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_501_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_501_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_501_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint8_t v___x_491_; 
v___x_491_ = lean_unbox(v_a_487_);
lean_dec(v_a_487_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = 1;
v___x_493_ = lean_box(v___x_492_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_493_);
v___x_495_ = v___x_489_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_box(v___x_483_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_497_);
v___x_499_ = v___x_489_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
return v___x_486_;
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec_ref(v_sig_480_);
v___x_502_ = lean_box(v___x_473_);
if (v_isShared_478_ == 0)
{
lean_ctor_set_tag(v___x_477_, 0);
lean_ctor_set(v___x_477_, 0, v___x_502_);
v___x_504_ = v___x_477_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_del_object(v___x_477_);
lean_dec(v_val_475_);
lean_dec(v_declName_461_);
goto v___jp_467_;
}
}
}
else
{
lean_dec(v___x_474_);
lean_dec(v_declName_461_);
goto v___jp_467_;
}
v___jp_467_:
{
uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = 0;
v___x_469_ = lean_box(v___x_468_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
return v_res_513_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_522_);
return v_res_524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_525_; lean_object* v___f_526_; 
v___x_525_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_526_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_526_, 0, v___x_525_);
return v___f_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___f_528_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_box(1);
v___x_531_ = l_Lean_registerEnvExtension___redArg(v___f_528_, v___x_529_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_533_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_534_, lean_object* v_opt_535_){
_start:
{
lean_object* v_name_536_; lean_object* v_defValue_537_; lean_object* v_map_538_; lean_object* v___x_539_; 
v_name_536_ = lean_ctor_get(v_opt_535_, 0);
v_defValue_537_ = lean_ctor_get(v_opt_535_, 1);
v_map_538_ = lean_ctor_get(v_opts_534_, 0);
v___x_539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_538_, v_name_536_);
if (lean_obj_tag(v___x_539_) == 0)
{
uint8_t v___x_540_; 
v___x_540_ = lean_unbox(v_defValue_537_);
return v___x_540_;
}
else
{
lean_object* v_val_541_; 
v_val_541_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_539_, 1);
if (lean_obj_tag(v_val_541_) == 1)
{
uint8_t v_v_542_; 
v_v_542_ = lean_ctor_get_uint8(v_val_541_, 0);
lean_dec_ref_known(v_val_541_, 0);
return v_v_542_;
}
else
{
uint8_t v___x_543_; 
lean_dec(v_val_541_);
v___x_543_ = lean_unbox(v_defValue_537_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_544_, lean_object* v_opt_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_544_, v_opt_545_);
lean_dec_ref(v_opt_545_);
lean_dec_ref(v_opts_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_opts_548_, lean_object* v_opt_549_){
_start:
{
lean_object* v_name_550_; lean_object* v_defValue_551_; lean_object* v_map_552_; lean_object* v___x_553_; 
v_name_550_ = lean_ctor_get(v_opt_549_, 0);
v_defValue_551_ = lean_ctor_get(v_opt_549_, 1);
v_map_552_ = lean_ctor_get(v_opts_548_, 0);
v___x_553_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_552_, v_name_550_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_inc(v_defValue_551_);
return v_defValue_551_;
}
else
{
lean_object* v_val_554_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v___x_553_, 1);
if (lean_obj_tag(v_val_554_) == 3)
{
lean_object* v_v_555_; 
v_v_555_ = lean_ctor_get(v_val_554_, 0);
lean_inc(v_v_555_);
lean_dec_ref_known(v_val_554_, 1);
return v_v_555_;
}
else
{
lean_dec(v_val_554_);
lean_inc(v_defValue_551_);
return v_defValue_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_opts_556_, lean_object* v_opt_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_556_, v_opt_557_);
lean_dec_ref(v_opt_557_);
lean_dec_ref(v_opts_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_562_, size_t v_sz_563_, size_t v_i_564_, lean_object* v_b_565_){
_start:
{
lean_object* v_a_567_; uint8_t v___x_571_; 
v___x_571_ = lean_usize_dec_lt(v_i_564_, v_sz_563_);
if (v___x_571_ == 0)
{
return v_b_565_;
}
else
{
lean_object* v_a_572_; lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v_map_575_; uint8_t v_hasTrace_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_589_; 
v_a_572_ = lean_array_uget_borrowed(v_as_562_, v_i_564_);
v_fst_573_ = lean_ctor_get(v_a_572_, 0);
v_snd_574_ = lean_ctor_get(v_a_572_, 1);
v_map_575_ = lean_ctor_get(v_b_565_, 0);
v_hasTrace_576_ = lean_ctor_get_uint8(v_b_565_, sizeof(void*)*1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_b_565_);
if (v_isSharedCheck_589_ == 0)
{
v___x_578_ = v_b_565_;
v_isShared_579_ = v_isSharedCheck_589_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_map_575_);
lean_dec(v_b_565_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_589_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; 
lean_inc(v_snd_574_);
lean_inc(v_fst_573_);
v___x_580_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_573_, v_snd_574_, v_map_575_);
if (v_hasTrace_576_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_584_; 
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_582_ = l_Lean_Name_isPrefixOf(v___x_581_, v_fst_573_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_580_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_580_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*1, v___x_582_);
v_a_567_ = v___x_584_;
goto v___jp_566_;
}
}
else
{
lean_object* v___x_587_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_580_);
v___x_587_ = v___x_578_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*1, v_hasTrace_576_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v_a_567_ = v___x_587_;
goto v___jp_566_;
}
}
}
}
v___jp_566_:
{
size_t v___x_568_; size_t v___x_569_; 
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_add(v_i_564_, v___x_568_);
v_i_564_ = v___x_569_;
v_b_565_ = v_a_567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_590_, lean_object* v_sz_591_, lean_object* v_i_592_, lean_object* v_b_593_){
_start:
{
size_t v_sz_boxed_594_; size_t v_i_boxed_595_; lean_object* v_res_596_; 
v_sz_boxed_594_ = lean_unbox_usize(v_sz_591_);
lean_dec(v_sz_591_);
v_i_boxed_595_ = lean_unbox_usize(v_i_592_);
lean_dec(v_i_592_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_as_590_, v_sz_boxed_594_, v_i_boxed_595_, v_b_593_);
lean_dec_ref(v_as_590_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_597_, lean_object* v_k_598_, uint8_t v_v_599_){
_start:
{
lean_object* v_map_600_; uint8_t v_hasTrace_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_615_; 
v_map_600_ = lean_ctor_get(v_o_597_, 0);
v_hasTrace_601_ = lean_ctor_get_uint8(v_o_597_, sizeof(void*)*1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_o_597_);
if (v_isSharedCheck_615_ == 0)
{
v___x_603_ = v_o_597_;
v_isShared_604_ = v_isSharedCheck_615_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_map_600_);
lean_dec(v_o_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_615_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_605_, 0, v_v_599_);
lean_inc(v_k_598_);
v___x_606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_598_, v___x_605_, v_map_600_);
if (v_hasTrace_601_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; lean_object* v___x_610_; 
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_608_ = l_Lean_Name_isPrefixOf(v___x_607_, v_k_598_);
lean_dec(v_k_598_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_606_);
v___x_610_ = v___x_603_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_606_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*1, v___x_608_);
return v___x_610_;
}
}
else
{
lean_object* v___x_613_; 
lean_dec(v_k_598_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_606_);
v___x_613_ = v___x_603_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_606_);
lean_ctor_set_uint8(v_reuseFailAlloc_614_, sizeof(void*)*1, v_hasTrace_601_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_616_, lean_object* v_k_617_, lean_object* v_v_618_){
_start:
{
uint8_t v_v_boxed_619_; lean_object* v_res_620_; 
v_v_boxed_619_ = lean_unbox(v_v_618_);
v_res_620_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_616_, v_k_617_, v_v_boxed_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_621_, lean_object* v_opt_622_, uint8_t v_val_623_){
_start:
{
lean_object* v_name_624_; lean_object* v___x_625_; 
v_name_624_ = lean_ctor_get(v_opt_622_, 0);
lean_inc(v_name_624_);
lean_dec_ref(v_opt_622_);
v___x_625_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_621_, v_name_624_, v_val_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_626_, lean_object* v_opt_627_, lean_object* v_val_628_){
_start:
{
uint8_t v_val_boxed_629_; lean_object* v_res_630_; 
v_val_boxed_629_ = lean_unbox(v_val_628_);
v_res_630_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_626_, v_opt_627_, v_val_boxed_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(lean_object* v_as_631_, size_t v_i_632_, size_t v_stop_633_, lean_object* v_b_634_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = lean_usize_dec_eq(v_i_632_, v_stop_633_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v_defValue_637_; uint8_t v___x_638_; lean_object* v___x_639_; size_t v___x_640_; size_t v___x_641_; 
v___x_636_ = lean_array_uget_borrowed(v_as_631_, v_i_632_);
v_defValue_637_ = lean_ctor_get(v___x_636_, 1);
v___x_638_ = lean_unbox(v_defValue_637_);
lean_inc(v___x_636_);
v___x_639_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_634_, v___x_636_, v___x_638_);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_632_, v___x_640_);
v_i_632_ = v___x_641_;
v_b_634_ = v___x_639_;
goto _start;
}
else
{
return v_b_634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(lean_object* v_as_643_, lean_object* v_i_644_, lean_object* v_stop_645_, lean_object* v_b_646_){
_start:
{
size_t v_i_boxed_647_; size_t v_stop_boxed_648_; lean_object* v_res_649_; 
v_i_boxed_647_ = lean_unbox_usize(v_i_644_);
lean_dec(v_i_644_);
v_stop_boxed_648_ = lean_unbox_usize(v_stop_645_);
lean_dec(v_stop_645_);
v_res_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v_as_643_, v_i_boxed_647_, v_stop_boxed_648_, v_b_646_);
lean_dec_ref(v_as_643_);
return v_res_649_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Array_instInhabited(lean_box(0));
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = l_Lean_Meta_eqnAffectingOptions;
v___x_657_ = lean_array_get_size(v___x_656_);
return v___x_657_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_nat_dec_lt(v___x_659_, v___x_658_);
return v___x_660_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_662_ = lean_nat_dec_le(v___x_661_, v___x_661_);
return v___x_662_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__7(void){
_start:
{
lean_object* v___x_663_; size_t v___x_664_; 
v___x_663_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_664_ = lean_usize_of_nat(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_665_, lean_object* v_act_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___y_673_; uint8_t v___y_674_; lean_object* v_fileName_675_; lean_object* v_fileMap_676_; lean_object* v_currRecDepth_677_; lean_object* v_ref_678_; lean_object* v_currNamespace_679_; lean_object* v_openDecls_680_; lean_object* v_initHeartbeats_681_; lean_object* v_maxHeartbeats_682_; lean_object* v_quotContext_683_; lean_object* v_currMacroScope_684_; lean_object* v_cancelTk_x3f_685_; uint8_t v_suppressElabErrors_686_; lean_object* v_inheritedTraceOptions_687_; lean_object* v___y_688_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_env_695_; lean_object* v___x_696_; lean_object* v_toEnvExtension_697_; lean_object* v_asyncMode_698_; lean_object* v_fileName_699_; lean_object* v_fileMap_700_; lean_object* v_options_701_; lean_object* v_currRecDepth_702_; lean_object* v_ref_703_; lean_object* v_currNamespace_704_; lean_object* v_openDecls_705_; lean_object* v_initHeartbeats_706_; lean_object* v_maxHeartbeats_707_; lean_object* v_quotContext_708_; lean_object* v_currMacroScope_709_; lean_object* v_cancelTk_x3f_710_; uint8_t v_suppressElabErrors_711_; lean_object* v_inheritedTraceOptions_712_; lean_object* v___y_714_; uint8_t v___y_715_; uint8_t v___y_716_; lean_object* v___y_738_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; 
v___x_693_ = lean_st_ref_get(v_a_670_);
v___x_694_ = lean_st_ref_get(v_a_670_);
v_env_695_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_env_695_);
lean_dec(v___x_693_);
v___x_696_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_697_ = lean_ctor_get(v___x_696_, 0);
v_asyncMode_698_ = lean_ctor_get(v_toEnvExtension_697_, 2);
v_fileName_699_ = lean_ctor_get(v_a_669_, 0);
v_fileMap_700_ = lean_ctor_get(v_a_669_, 1);
v_options_701_ = lean_ctor_get(v_a_669_, 2);
v_currRecDepth_702_ = lean_ctor_get(v_a_669_, 3);
v_ref_703_ = lean_ctor_get(v_a_669_, 5);
v_currNamespace_704_ = lean_ctor_get(v_a_669_, 6);
v_openDecls_705_ = lean_ctor_get(v_a_669_, 7);
v_initHeartbeats_706_ = lean_ctor_get(v_a_669_, 8);
v_maxHeartbeats_707_ = lean_ctor_get(v_a_669_, 9);
v_quotContext_708_ = lean_ctor_get(v_a_669_, 10);
v_currMacroScope_709_ = lean_ctor_get(v_a_669_, 11);
v_cancelTk_x3f_710_ = lean_ctor_get(v_a_669_, 12);
v_suppressElabErrors_711_ = lean_ctor_get_uint8(v_a_669_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_712_ = lean_ctor_get(v_a_669_, 13);
v___x_743_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_744_ = 0;
v___x_745_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_743_, v___x_696_, v_env_695_, v_declName_665_, v_asyncMode_698_, v___x_744_);
if (lean_obj_tag(v___x_745_) == 1)
{
lean_object* v_val_746_; lean_object* v___y_748_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v___x_745_, 1);
v___x_752_ = l_Lean_Meta_eqnAffectingOptions;
v___x_753_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_753_ == 0)
{
lean_inc_ref(v_options_701_);
v___y_748_ = v_options_701_;
goto v___jp_747_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_754_ == 0)
{
if (v___x_753_ == 0)
{
lean_inc_ref(v_options_701_);
v___y_748_ = v_options_701_;
goto v___jp_747_;
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_701_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_752_, v___x_755_, v___x_756_, v_options_701_);
v___y_748_ = v___x_757_;
goto v___jp_747_;
}
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_701_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_752_, v___x_758_, v___x_759_, v_options_701_);
v___y_748_ = v___x_760_;
goto v___jp_747_;
}
}
v___jp_747_:
{
size_t v_sz_749_; size_t v___x_750_; lean_object* v___x_751_; 
v_sz_749_ = lean_array_size(v_val_746_);
v___x_750_ = ((size_t)0ULL);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_746_, v_sz_749_, v___x_750_, v___y_748_);
lean_dec(v_val_746_);
v___y_738_ = v___x_751_;
goto v___jp_737_;
}
}
else
{
lean_object* v___x_761_; uint8_t v___x_762_; 
lean_dec(v___x_745_);
v___x_761_ = l_Lean_Meta_eqnAffectingOptions;
v___x_762_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_762_ == 0)
{
lean_inc_ref(v_options_701_);
v___y_738_ = v_options_701_;
goto v___jp_737_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_763_ == 0)
{
if (v___x_762_ == 0)
{
lean_inc_ref(v_options_701_);
v___y_738_ = v_options_701_;
goto v___jp_737_;
}
else
{
size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_701_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_761_, v___x_764_, v___x_765_, v_options_701_);
v___y_738_ = v___x_766_;
goto v___jp_737_;
}
}
else
{
size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((size_t)0ULL);
v___x_768_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_701_);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_761_, v___x_767_, v___x_768_, v_options_701_);
v___y_738_ = v___x_769_;
goto v___jp_737_;
}
}
}
v___jp_672_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_689_ = l_Lean_maxRecDepth;
v___x_690_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_673_, v___x_689_);
lean_inc_ref(v_inheritedTraceOptions_687_);
lean_inc(v_cancelTk_x3f_685_);
lean_inc(v_currMacroScope_684_);
lean_inc(v_quotContext_683_);
lean_inc(v_maxHeartbeats_682_);
lean_inc(v_initHeartbeats_681_);
lean_inc(v_openDecls_680_);
lean_inc(v_currNamespace_679_);
lean_inc(v_ref_678_);
lean_inc(v_currRecDepth_677_);
lean_inc_ref(v_fileMap_676_);
lean_inc_ref(v_fileName_675_);
v___x_691_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_691_, 0, v_fileName_675_);
lean_ctor_set(v___x_691_, 1, v_fileMap_676_);
lean_ctor_set(v___x_691_, 2, v___y_673_);
lean_ctor_set(v___x_691_, 3, v_currRecDepth_677_);
lean_ctor_set(v___x_691_, 4, v___x_690_);
lean_ctor_set(v___x_691_, 5, v_ref_678_);
lean_ctor_set(v___x_691_, 6, v_currNamespace_679_);
lean_ctor_set(v___x_691_, 7, v_openDecls_680_);
lean_ctor_set(v___x_691_, 8, v_initHeartbeats_681_);
lean_ctor_set(v___x_691_, 9, v_maxHeartbeats_682_);
lean_ctor_set(v___x_691_, 10, v_quotContext_683_);
lean_ctor_set(v___x_691_, 11, v_currMacroScope_684_);
lean_ctor_set(v___x_691_, 12, v_cancelTk_x3f_685_);
lean_ctor_set(v___x_691_, 13, v_inheritedTraceOptions_687_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*14, v___y_674_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*14 + 1, v_suppressElabErrors_686_);
lean_inc(v___y_688_);
lean_inc(v_a_668_);
lean_inc_ref(v_a_667_);
v___x_692_ = lean_apply_5(v_act_666_, v_a_667_, v_a_668_, v___x_691_, v___y_688_, lean_box(0));
return v___x_692_;
}
v___jp_713_:
{
if (v___y_716_ == 0)
{
lean_object* v___x_717_; lean_object* v_env_718_; lean_object* v_nextMacroScope_719_; lean_object* v_ngen_720_; lean_object* v_auxDeclNGen_721_; lean_object* v_traceState_722_; lean_object* v_messages_723_; lean_object* v_infoState_724_; lean_object* v_snapshotTasks_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_735_; 
v___x_717_ = lean_st_ref_take(v_a_670_);
v_env_718_ = lean_ctor_get(v___x_717_, 0);
v_nextMacroScope_719_ = lean_ctor_get(v___x_717_, 1);
v_ngen_720_ = lean_ctor_get(v___x_717_, 2);
v_auxDeclNGen_721_ = lean_ctor_get(v___x_717_, 3);
v_traceState_722_ = lean_ctor_get(v___x_717_, 4);
v_messages_723_ = lean_ctor_get(v___x_717_, 6);
v_infoState_724_ = lean_ctor_get(v___x_717_, 7);
v_snapshotTasks_725_ = lean_ctor_get(v___x_717_, 8);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v___x_717_, 5);
lean_dec(v_unused_736_);
v___x_727_ = v___x_717_;
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snapshotTasks_725_);
lean_inc(v_infoState_724_);
lean_inc(v_messages_723_);
lean_inc(v_traceState_722_);
lean_inc(v_auxDeclNGen_721_);
lean_inc(v_ngen_720_);
lean_inc(v_nextMacroScope_719_);
lean_inc(v_env_718_);
lean_dec(v___x_717_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = l_Lean_Kernel_enableDiag(v_env_718_, v___y_715_);
v___x_730_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 5, v___x_730_);
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_nextMacroScope_719_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_ngen_720_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_auxDeclNGen_721_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_traceState_722_);
lean_ctor_set(v_reuseFailAlloc_734_, 5, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_734_, 6, v_messages_723_);
lean_ctor_set(v_reuseFailAlloc_734_, 7, v_infoState_724_);
lean_ctor_set(v_reuseFailAlloc_734_, 8, v_snapshotTasks_725_);
v___x_732_ = v_reuseFailAlloc_734_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_st_ref_set(v_a_670_, v___x_732_);
v___y_673_ = v___y_714_;
v___y_674_ = v___y_715_;
v_fileName_675_ = v_fileName_699_;
v_fileMap_676_ = v_fileMap_700_;
v_currRecDepth_677_ = v_currRecDepth_702_;
v_ref_678_ = v_ref_703_;
v_currNamespace_679_ = v_currNamespace_704_;
v_openDecls_680_ = v_openDecls_705_;
v_initHeartbeats_681_ = v_initHeartbeats_706_;
v_maxHeartbeats_682_ = v_maxHeartbeats_707_;
v_quotContext_683_ = v_quotContext_708_;
v_currMacroScope_684_ = v_currMacroScope_709_;
v_cancelTk_x3f_685_ = v_cancelTk_x3f_710_;
v_suppressElabErrors_686_ = v_suppressElabErrors_711_;
v_inheritedTraceOptions_687_ = v_inheritedTraceOptions_712_;
v___y_688_ = v_a_670_;
goto v___jp_672_;
}
}
}
else
{
v___y_673_ = v___y_714_;
v___y_674_ = v___y_715_;
v_fileName_675_ = v_fileName_699_;
v_fileMap_676_ = v_fileMap_700_;
v_currRecDepth_677_ = v_currRecDepth_702_;
v_ref_678_ = v_ref_703_;
v_currNamespace_679_ = v_currNamespace_704_;
v_openDecls_680_ = v_openDecls_705_;
v_initHeartbeats_681_ = v_initHeartbeats_706_;
v_maxHeartbeats_682_ = v_maxHeartbeats_707_;
v_quotContext_683_ = v_quotContext_708_;
v_currMacroScope_684_ = v_currMacroScope_709_;
v_cancelTk_x3f_685_ = v_cancelTk_x3f_710_;
v_suppressElabErrors_686_ = v_suppressElabErrors_711_;
v_inheritedTraceOptions_687_ = v_inheritedTraceOptions_712_;
v___y_688_ = v_a_670_;
goto v___jp_672_;
}
}
v___jp_737_:
{
lean_object* v_env_739_; lean_object* v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; 
v_env_739_ = lean_ctor_get(v___x_694_, 0);
lean_inc_ref(v_env_739_);
lean_dec(v___x_694_);
v___x_740_ = l_Lean_diagnostics;
v___x_741_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_738_, v___x_740_);
v___x_742_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_739_);
lean_dec_ref(v_env_739_);
if (v___x_742_ == 0)
{
if (v___x_741_ == 0)
{
v___y_673_ = v___y_738_;
v___y_674_ = v___x_741_;
v_fileName_675_ = v_fileName_699_;
v_fileMap_676_ = v_fileMap_700_;
v_currRecDepth_677_ = v_currRecDepth_702_;
v_ref_678_ = v_ref_703_;
v_currNamespace_679_ = v_currNamespace_704_;
v_openDecls_680_ = v_openDecls_705_;
v_initHeartbeats_681_ = v_initHeartbeats_706_;
v_maxHeartbeats_682_ = v_maxHeartbeats_707_;
v_quotContext_683_ = v_quotContext_708_;
v_currMacroScope_684_ = v_currMacroScope_709_;
v_cancelTk_x3f_685_ = v_cancelTk_x3f_710_;
v_suppressElabErrors_686_ = v_suppressElabErrors_711_;
v_inheritedTraceOptions_687_ = v_inheritedTraceOptions_712_;
v___y_688_ = v_a_670_;
goto v___jp_672_;
}
else
{
v___y_714_ = v___y_738_;
v___y_715_ = v___x_741_;
v___y_716_ = v___x_742_;
goto v___jp_713_;
}
}
else
{
v___y_714_ = v___y_738_;
v___y_715_ = v___x_741_;
v___y_716_ = v___x_741_;
goto v___jp_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_770_, lean_object* v_act_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_770_, v_act_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_778_, lean_object* v_declName_779_, lean_object* v_act_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_779_, v_act_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_787_, lean_object* v_declName_788_, lean_object* v_act_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_787_, v_declName_788_, v_act_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; lean_object* v_env_800_; lean_object* v_toConstantVal_801_; lean_object* v_value_802_; lean_object* v_all_803_; uint8_t v___y_805_; lean_object* v_type_813_; uint8_t v___x_814_; 
v___x_799_ = lean_st_ref_get(v___y_797_);
v_env_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc_ref_n(v_env_800_, 2);
lean_dec(v___x_799_);
v_toConstantVal_801_ = lean_ctor_get(v_thm_796_, 0);
v_value_802_ = lean_ctor_get(v_thm_796_, 1);
v_all_803_ = lean_ctor_get(v_thm_796_, 2);
v_type_813_ = lean_ctor_get(v_toConstantVal_801_, 2);
v___x_814_ = l_Lean_Environment_hasUnsafe(v_env_800_, v_type_813_);
if (v___x_814_ == 0)
{
uint8_t v___x_815_; 
v___x_815_ = l_Lean_Environment_hasUnsafe(v_env_800_, v_value_802_);
v___y_805_ = v___x_815_;
goto v___jp_804_;
}
else
{
lean_dec_ref(v_env_800_);
v___y_805_ = v___x_814_;
goto v___jp_804_;
}
v___jp_804_:
{
if (v___y_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_806_, 0, v_thm_796_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_inc(v_all_803_);
lean_inc_ref(v_value_802_);
lean_inc_ref(v_toConstantVal_801_);
lean_dec_ref(v_thm_796_);
v___x_808_ = lean_box(0);
v___x_809_ = 0;
v___x_810_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_810_, 0, v_toConstantVal_801_);
lean_ctor_set(v___x_810_, 1, v_value_802_);
lean_ctor_set(v___x_810_, 2, v___x_808_);
lean_ctor_set(v___x_810_, 3, v_all_803_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*4, v___x_809_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_816_, v___y_817_);
lean_dec(v___y_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_820_, v___y_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_834_, lean_object* v_b_835_, lean_object* v_c_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
v___x_842_ = lean_apply_7(v_k_834_, v_b_835_, v_c_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, lean_box(0));
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_843_, lean_object* v_b_844_, lean_object* v_c_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_843_, v_b_844_, v_c_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_852_, lean_object* v_k_853_, uint8_t v_cleanupAnnotations_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___f_860_; uint8_t v___x_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___f_860_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_860_, 0, v_k_853_);
v___x_861_ = 1;
v___x_862_ = 0;
v___x_863_ = lean_box(0);
v___x_864_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_852_, v___x_861_, v___x_862_, v___x_861_, v___x_862_, v___x_863_, v___f_860_, v_cleanupAnnotations_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_864_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_864_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_881_, lean_object* v_k_882_, lean_object* v_cleanupAnnotations_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_889_; lean_object* v_res_890_; 
v_cleanupAnnotations_boxed_889_ = lean_unbox(v_cleanupAnnotations_883_);
v_res_890_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_881_, v_k_882_, v_cleanupAnnotations_boxed_889_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_891_, lean_object* v_e_892_, lean_object* v_k_893_, uint8_t v_cleanupAnnotations_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_892_, v_k_893_, v_cleanupAnnotations_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_901_, lean_object* v_e_902_, lean_object* v_k_903_, lean_object* v_cleanupAnnotations_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_910_; lean_object* v_res_911_; 
v_cleanupAnnotations_boxed_910_ = lean_unbox(v_cleanupAnnotations_904_);
v_res_911_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_901_, v_e_902_, v_k_903_, v_cleanupAnnotations_boxed_910_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
if (lean_obj_tag(v_a_912_) == 0)
{
lean_object* v___x_914_; 
v___x_914_ = l_List_reverse___redArg(v_a_913_);
return v___x_914_;
}
else
{
lean_object* v_head_915_; lean_object* v_tail_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_925_; 
v_head_915_ = lean_ctor_get(v_a_912_, 0);
v_tail_916_ = lean_ctor_get(v_a_912_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_a_912_);
if (v_isSharedCheck_925_ == 0)
{
v___x_918_ = v_a_912_;
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_tail_916_);
lean_inc(v_head_915_);
lean_dec(v_a_912_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = l_Lean_mkLevelParam(v_head_915_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_a_913_);
lean_ctor_set(v___x_918_, 0, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_913_);
v___x_922_ = v_reuseFailAlloc_924_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
v_a_912_ = v_tail_916_;
v_a_913_ = v___x_922_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_926_, lean_object* v_name_927_, lean_object* v_xs_928_, lean_object* v_body_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_name_935_; lean_object* v_levelParams_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_1006_; 
v_name_935_ = lean_ctor_get(v_toConstantVal_926_, 0);
v_levelParams_936_ = lean_ctor_get(v_toConstantVal_926_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_toConstantVal_926_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v_toConstantVal_926_, 2);
lean_dec(v_unused_1007_);
v___x_938_ = v_toConstantVal_926_;
v_isShared_939_ = v_isSharedCheck_1006_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_levelParams_936_);
lean_inc(v_name_935_);
lean_dec(v_toConstantVal_926_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_1006_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_lhs_943_; lean_object* v___x_944_; 
v___x_940_ = lean_box(0);
lean_inc(v_levelParams_936_);
v___x_941_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_936_, v___x_940_);
v___x_942_ = l_Lean_mkConst(v_name_935_, v___x_941_);
v_lhs_943_ = l_Lean_mkAppN(v___x_942_, v_xs_928_);
lean_inc_ref(v_lhs_943_);
v___x_944_ = l_Lean_Meta_mkEq(v_lhs_943_, v_body_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; uint8_t v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = 0;
v___x_947_ = 1;
v___x_948_ = 1;
v___x_949_ = l_Lean_Meta_mkForallFVars(v_xs_928_, v_a_945_, v___x_946_, v___x_947_, v___x_947_, v___x_948_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = l_Lean_Meta_letToHave(v_a_950_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = l_Lean_Meta_mkEqRefl(v_lhs_943_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = l_Lean_Meta_mkLambdaFVars(v_xs_928_, v_a_954_, v___x_946_, v___x_947_, v___x_946_, v___x_947_, v___x_948_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
lean_inc(v_name_927_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 2, v_a_952_);
lean_ctor_set(v___x_938_, 0, v_name_927_);
v___x_958_ = v___x_938_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_name_927_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_levelParams_936_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_a_952_);
v___x_958_ = v_reuseFailAlloc_965_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_963_; 
lean_inc(v_name_927_);
v___x_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_959_, 0, v_name_927_);
lean_ctor_set(v___x_959_, 1, v___x_940_);
v___x_960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v_a_956_);
lean_ctor_set(v___x_960_, 2, v___x_959_);
v___x_961_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_960_, v___y_933_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
v___x_963_ = l_Lean_addDecl(v_a_962_, v___x_946_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v___x_964_; 
lean_dec_ref_known(v___x_963_, 1);
v___x_964_ = l_Lean_inferDefEqAttr(v_name_927_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_964_;
}
else
{
lean_dec(v_name_927_);
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_a_952_);
lean_del_object(v___x_938_);
lean_dec(v_levelParams_936_);
lean_dec(v_name_927_);
v_a_966_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_955_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_955_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_a_952_);
lean_del_object(v___x_938_);
lean_dec(v_levelParams_936_);
lean_dec(v_name_927_);
v_a_974_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_953_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_953_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v_lhs_943_);
lean_del_object(v___x_938_);
lean_dec(v_levelParams_936_);
lean_dec(v_name_927_);
v_a_982_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_951_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_951_);
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
lean_dec_ref(v_lhs_943_);
lean_del_object(v___x_938_);
lean_dec(v_levelParams_936_);
lean_dec(v_name_927_);
v_a_990_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_949_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_949_);
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
lean_dec_ref(v_lhs_943_);
lean_del_object(v___x_938_);
lean_dec(v_levelParams_936_);
lean_dec(v_name_927_);
v_a_998_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_944_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_944_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1008_, lean_object* v_name_1009_, lean_object* v_xs_1010_, lean_object* v_body_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1008_, v_name_1009_, v_xs_1010_, v_body_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_xs_1010_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1018_, lean_object* v_info_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_toConstantVal_1025_; lean_object* v_value_1026_; lean_object* v___f_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; 
v_toConstantVal_1025_ = lean_ctor_get(v_info_1019_, 0);
lean_inc_ref(v_toConstantVal_1025_);
v_value_1026_ = lean_ctor_get(v_info_1019_, 1);
lean_inc_ref(v_value_1026_);
lean_dec_ref(v_info_1019_);
v___f_1027_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1027_, 0, v_toConstantVal_1025_);
lean_closure_set(v___f_1027_, 1, v_name_1018_);
v___x_1028_ = 1;
v___x_1029_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1026_, v___f_1027_, v___x_1028_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1030_, lean_object* v_info_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1030_, v_info_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1038_, lean_object* v_name_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1048_; lean_object* v_env_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1048_ = lean_st_ref_get(v_a_1043_);
v_env_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc_ref(v_env_1049_);
lean_dec(v___x_1048_);
v___x_1050_ = 0;
lean_inc(v_declName_1038_);
v___x_1051_ = l_Lean_Environment_find_x3f(v_env_1049_, v_declName_1038_, v___x_1050_);
if (lean_obj_tag(v___x_1051_) == 1)
{
lean_object* v_val_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1079_; 
v_val_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1079_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_val_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1079_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
if (lean_obj_tag(v_val_1052_) == 1)
{
lean_object* v_val_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_val_1056_ = lean_ctor_get(v_val_1052_, 0);
lean_inc_ref(v_val_1056_);
lean_dec_ref_known(v_val_1052_, 1);
lean_inc_n(v_name_1039_, 2);
v___x_1057_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1057_, 0, v_name_1039_);
lean_closure_set(v___x_1057_, 1, v_val_1056_);
lean_inc(v_declName_1038_);
v___x_1058_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1058_, 0, lean_box(0));
lean_closure_set(v___x_1058_, 1, v_declName_1038_);
lean_closure_set(v___x_1058_, 2, v___x_1057_);
v___x_1059_ = l_Lean_Meta_realizeConst(v_declName_1038_, v_name_1039_, v___x_1058_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1069_; 
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v___x_1059_, 0);
lean_dec(v_unused_1070_);
v___x_1061_ = v___x_1059_;
v_isShared_1062_ = v_isSharedCheck_1069_;
goto v_resetjp_1060_;
}
else
{
lean_dec(v___x_1059_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1069_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v_name_1039_);
v___x_1064_ = v___x_1054_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_name_1039_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1064_);
v___x_1066_ = v___x_1061_;
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
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_1054_);
lean_dec(v_name_1039_);
v_a_1071_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1059_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1059_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_del_object(v___x_1054_);
lean_dec(v_val_1052_);
lean_dec(v_name_1039_);
lean_dec(v_declName_1038_);
goto v___jp_1045_;
}
}
}
else
{
lean_dec(v___x_1051_);
lean_dec(v_name_1039_);
lean_dec(v_declName_1038_);
goto v___jp_1045_;
}
v___jp_1045_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1080_, lean_object* v_name_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1080_, v_name_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1088_, lean_object* v_vals_1089_, lean_object* v_i_1090_, lean_object* v_k_1091_){
_start:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = lean_array_get_size(v_keys_1088_);
v___x_1093_ = lean_nat_dec_lt(v_i_1090_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec(v_i_1090_);
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
else
{
lean_object* v_k_x27_1095_; uint8_t v___x_1096_; 
v_k_x27_1095_ = lean_array_fget_borrowed(v_keys_1088_, v_i_1090_);
v___x_1096_ = lean_name_eq(v_k_1091_, v_k_x27_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(1u);
v___x_1098_ = lean_nat_add(v_i_1090_, v___x_1097_);
lean_dec(v_i_1090_);
v_i_1090_ = v___x_1098_;
goto _start;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_array_fget_borrowed(v_vals_1089_, v_i_1090_);
lean_dec(v_i_1090_);
lean_inc(v___x_1100_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1102_, lean_object* v_vals_1103_, lean_object* v_i_1104_, lean_object* v_k_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1102_, v_vals_1103_, v_i_1104_, v_k_1105_);
lean_dec(v_k_1105_);
lean_dec_ref(v_vals_1103_);
lean_dec_ref(v_keys_1102_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1107_, size_t v_x_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 0)
{
lean_object* v_es_1110_; lean_object* v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; lean_object* v_j_1114_; lean_object* v___x_1115_; 
v_es_1110_ = lean_ctor_get(v_x_1107_, 0);
v___x_1111_ = lean_box(2);
v___x_1112_ = ((size_t)31ULL);
v___x_1113_ = lean_usize_land(v_x_1108_, v___x_1112_);
v_j_1114_ = lean_usize_to_nat(v___x_1113_);
v___x_1115_ = lean_array_get_borrowed(v___x_1111_, v_es_1110_, v_j_1114_);
lean_dec(v_j_1114_);
switch(lean_obj_tag(v___x_1115_))
{
case 0:
{
lean_object* v_key_1116_; lean_object* v_val_1117_; uint8_t v___x_1118_; 
v_key_1116_ = lean_ctor_get(v___x_1115_, 0);
v_val_1117_ = lean_ctor_get(v___x_1115_, 1);
v___x_1118_ = lean_name_eq(v_x_1109_, v_key_1116_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_box(0);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; 
lean_inc(v_val_1117_);
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_val_1117_);
return v___x_1120_;
}
}
case 1:
{
lean_object* v_node_1121_; size_t v___x_1122_; size_t v___x_1123_; 
v_node_1121_ = lean_ctor_get(v___x_1115_, 0);
v___x_1122_ = ((size_t)5ULL);
v___x_1123_ = lean_usize_shift_right(v_x_1108_, v___x_1122_);
v_x_1107_ = v_node_1121_;
v_x_1108_ = v___x_1123_;
goto _start;
}
default: 
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_box(0);
return v___x_1125_;
}
}
}
else
{
lean_object* v_ks_1126_; lean_object* v_vs_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_ks_1126_ = lean_ctor_get(v_x_1107_, 0);
v_vs_1127_ = lean_ctor_get(v_x_1107_, 1);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1126_, v_vs_1127_, v___x_1128_, v_x_1109_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
size_t v_x_339__boxed_1133_; lean_object* v_res_1134_; 
v_x_339__boxed_1133_ = lean_unbox_usize(v_x_1131_);
lean_dec(v_x_1131_);
v_res_1134_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1130_, v_x_339__boxed_1133_, v_x_1132_);
lean_dec(v_x_1132_);
lean_dec_ref(v_x_1130_);
return v_res_1134_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1135_; uint64_t v___x_1136_; 
v___x_1135_ = lean_unsigned_to_nat(1723u);
v___x_1136_ = lean_uint64_of_nat(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
uint64_t v___y_1140_; 
if (lean_obj_tag(v_x_1138_) == 0)
{
uint64_t v___x_1143_; 
v___x_1143_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1140_ = v___x_1143_;
goto v___jp_1139_;
}
else
{
uint64_t v_hash_1144_; 
v_hash_1144_ = lean_ctor_get_uint64(v_x_1138_, sizeof(void*)*2);
v___y_1140_ = v_hash_1144_;
goto v___jp_1139_;
}
v___jp_1139_:
{
size_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_uint64_to_usize(v___y_1140_);
v___x_1142_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1137_, v___x_1141_, v_x_1138_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1145_, v_x_1146_);
lean_dec(v_x_1146_);
lean_dec_ref(v_x_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1151_; lean_object* v_env_1152_; lean_object* v___x_1153_; lean_object* v_asyncMode_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1151_ = lean_st_ref_get(v_a_1149_);
v_env_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_ref(v_env_1152_);
lean_dec(v___x_1151_);
v___x_1153_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1154_ = lean_ctor_get(v___x_1153_, 2);
v___x_1155_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1156_ = lean_box(0);
v___x_1157_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1155_, v___x_1153_, v_env_1152_, v_asyncMode_1154_, v___x_1156_);
v___x_1158_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1157_, v_thmName_1148_);
lean_dec(v___x_1157_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec(v_thmName_1160_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1164_, v_a_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_thmName_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1175_, v_x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1178_, v_x_1179_, v_x_1180_);
lean_dec(v_x_1180_);
lean_dec_ref(v_x_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1182_, lean_object* v_x_1183_, size_t v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1183_, v_x_1184_, v_x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
size_t v_x_438__boxed_1191_; lean_object* v_res_1192_; 
v_x_438__boxed_1191_ = lean_unbox_usize(v_x_1189_);
lean_dec(v_x_1189_);
v_res_1192_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1187_, v_x_1188_, v_x_438__boxed_1191_, v_x_1190_);
lean_dec(v_x_1190_);
lean_dec_ref(v_x_1188_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1193_, lean_object* v_keys_1194_, lean_object* v_vals_1195_, lean_object* v_heq_1196_, lean_object* v_i_1197_, lean_object* v_k_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1194_, v_vals_1195_, v_i_1197_, v_k_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1200_, lean_object* v_keys_1201_, lean_object* v_vals_1202_, lean_object* v_heq_1203_, lean_object* v_i_1204_, lean_object* v_k_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1200_, v_keys_1201_, v_vals_1202_, v_heq_1203_, v_i_1204_, v_k_1205_);
lean_dec(v_k_1205_);
lean_dec_ref(v_vals_1202_);
lean_dec_ref(v_keys_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1207_, lean_object* v_i_1208_, lean_object* v_k_1209_){
_start:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_array_get_size(v_keys_1207_);
v___x_1211_ = lean_nat_dec_lt(v_i_1208_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec(v_i_1208_);
return v___x_1211_;
}
else
{
lean_object* v_k_x27_1212_; uint8_t v___x_1213_; 
v_k_x27_1212_ = lean_array_fget_borrowed(v_keys_1207_, v_i_1208_);
v___x_1213_ = lean_name_eq(v_k_1209_, v_k_x27_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = lean_nat_add(v_i_1208_, v___x_1214_);
lean_dec(v_i_1208_);
v_i_1208_ = v___x_1215_;
goto _start;
}
else
{
lean_dec(v_i_1208_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1217_, lean_object* v_i_1218_, lean_object* v_k_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1217_, v_i_1218_, v_k_1219_);
lean_dec(v_k_1219_);
lean_dec_ref(v_keys_1217_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1222_, size_t v_x_1223_, lean_object* v_x_1224_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
lean_object* v_es_1225_; lean_object* v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; lean_object* v_j_1229_; lean_object* v___x_1230_; 
v_es_1225_ = lean_ctor_get(v_x_1222_, 0);
v___x_1226_ = lean_box(2);
v___x_1227_ = ((size_t)31ULL);
v___x_1228_ = lean_usize_land(v_x_1223_, v___x_1227_);
v_j_1229_ = lean_usize_to_nat(v___x_1228_);
v___x_1230_ = lean_array_get_borrowed(v___x_1226_, v_es_1225_, v_j_1229_);
lean_dec(v_j_1229_);
switch(lean_obj_tag(v___x_1230_))
{
case 0:
{
lean_object* v_key_1231_; uint8_t v___x_1232_; 
v_key_1231_ = lean_ctor_get(v___x_1230_, 0);
v___x_1232_ = lean_name_eq(v_x_1224_, v_key_1231_);
return v___x_1232_;
}
case 1:
{
lean_object* v_node_1233_; size_t v___x_1234_; size_t v___x_1235_; 
v_node_1233_ = lean_ctor_get(v___x_1230_, 0);
v___x_1234_ = ((size_t)5ULL);
v___x_1235_ = lean_usize_shift_right(v_x_1223_, v___x_1234_);
v_x_1222_ = v_node_1233_;
v_x_1223_ = v___x_1235_;
goto _start;
}
default: 
{
uint8_t v___x_1237_; 
v___x_1237_ = 0;
return v___x_1237_;
}
}
}
else
{
lean_object* v_ks_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_ks_1238_ = lean_ctor_get(v_x_1222_, 0);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1238_, v___x_1239_, v_x_1224_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
size_t v_x_325__boxed_1244_; uint8_t v_res_1245_; lean_object* v_r_1246_; 
v_x_325__boxed_1244_ = lean_unbox_usize(v_x_1242_);
lean_dec(v_x_1242_);
v_res_1245_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1241_, v_x_325__boxed_1244_, v_x_1243_);
lean_dec(v_x_1243_);
lean_dec_ref(v_x_1241_);
v_r_1246_ = lean_box(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint64_t v___y_1250_; 
if (lean_obj_tag(v_x_1248_) == 0)
{
uint64_t v___x_1253_; 
v___x_1253_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1250_ = v___x_1253_;
goto v___jp_1249_;
}
else
{
uint64_t v_hash_1254_; 
v_hash_1254_ = lean_ctor_get_uint64(v_x_1248_, sizeof(void*)*2);
v___y_1250_ = v_hash_1254_;
goto v___jp_1249_;
}
v___jp_1249_:
{
size_t v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_uint64_to_usize(v___y_1250_);
v___x_1252_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1247_, v___x_1251_, v_x_1248_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1255_, v_x_1256_);
lean_dec(v_x_1256_);
lean_dec_ref(v_x_1255_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v_env_1263_; lean_object* v___x_1264_; lean_object* v_asyncMode_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1262_ = lean_st_ref_get(v_a_1260_);
v_env_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc_ref(v_env_1263_);
lean_dec(v___x_1262_);
v___x_1264_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1265_ = lean_ctor_get(v___x_1264_, 2);
v___x_1266_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1267_ = lean_box(0);
v___x_1268_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1266_, v___x_1264_, v_env_1263_, v_asyncMode_1265_, v___x_1267_);
v___x_1269_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1268_, v_thmName_1259_);
lean_dec(v___x_1268_);
v___x_1270_ = lean_box(v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec(v_thmName_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1276_, v_a_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Meta_isEqnThm(v_thmName_1281_, v_a_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_thmName_1281_);
return v_res_1285_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1287_, v_x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
uint8_t v_res_1293_; lean_object* v_r_1294_; 
v_res_1293_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1290_, v_x_1291_, v_x_1292_);
lean_dec(v_x_1292_);
lean_dec_ref(v_x_1291_);
v_r_1294_ = lean_box(v_res_1293_);
return v_r_1294_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1295_, lean_object* v_x_1296_, size_t v_x_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1296_, v_x_1297_, v_x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
size_t v_x_417__boxed_1304_; uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_x_417__boxed_1304_ = lean_unbox_usize(v_x_1302_);
lean_dec(v_x_1302_);
v_res_1305_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1300_, v_x_1301_, v_x_417__boxed_1304_, v_x_1303_);
lean_dec(v_x_1303_);
lean_dec_ref(v_x_1301_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1307_, lean_object* v_keys_1308_, lean_object* v_vals_1309_, lean_object* v_heq_1310_, lean_object* v_i_1311_, lean_object* v_k_1312_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1308_, v_i_1311_, v_k_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1314_, lean_object* v_keys_1315_, lean_object* v_vals_1316_, lean_object* v_heq_1317_, lean_object* v_i_1318_, lean_object* v_k_1319_){
_start:
{
uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_res_1320_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1314_, v_keys_1315_, v_vals_1316_, v_heq_1317_, v_i_1318_, v_k_1319_);
lean_dec(v_k_1319_);
lean_dec_ref(v_vals_1316_);
lean_dec_ref(v_keys_1315_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_){
_start:
{
lean_object* v_ks_1326_; lean_object* v_vs_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1351_; 
v_ks_1326_ = lean_ctor_get(v_x_1322_, 0);
v_vs_1327_ = lean_ctor_get(v_x_1322_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1329_ = v_x_1322_;
v_isShared_1330_ = v_isSharedCheck_1351_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_vs_1327_);
lean_inc(v_ks_1326_);
lean_dec(v_x_1322_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1351_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = lean_array_get_size(v_ks_1326_);
v___x_1332_ = lean_nat_dec_lt(v_x_1323_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_dec(v_x_1323_);
v___x_1333_ = lean_array_push(v_ks_1326_, v_x_1324_);
v___x_1334_ = lean_array_push(v_vs_1327_, v_x_1325_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v___x_1334_);
lean_ctor_set(v___x_1329_, 0, v___x_1333_);
v___x_1336_ = v___x_1329_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v_k_x27_1338_; uint8_t v___x_1339_; 
v_k_x27_1338_ = lean_array_fget_borrowed(v_ks_1326_, v_x_1323_);
v___x_1339_ = lean_name_eq(v_x_1324_, v_k_x27_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1341_; 
if (v_isShared_1330_ == 0)
{
v___x_1341_ = v___x_1329_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_ks_1326_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_vs_1327_);
v___x_1341_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_nat_add(v_x_1323_, v___x_1342_);
lean_dec(v_x_1323_);
v_x_1322_ = v___x_1341_;
v_x_1323_ = v___x_1343_;
goto _start;
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = lean_array_fset(v_ks_1326_, v_x_1323_, v_x_1324_);
v___x_1347_ = lean_array_fset(v_vs_1327_, v_x_1323_, v_x_1325_);
lean_dec(v_x_1323_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v___x_1347_);
lean_ctor_set(v___x_1329_, 0, v___x_1346_);
v___x_1349_ = v___x_1329_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1352_, lean_object* v_k_1353_, lean_object* v_v_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1352_, v___x_1355_, v_k_1353_, v_v_1354_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1358_, size_t v_x_1359_, size_t v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_object* v_es_1363_; size_t v___x_1364_; size_t v___x_1365_; lean_object* v_j_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_es_1363_ = lean_ctor_get(v_x_1358_, 0);
v___x_1364_ = ((size_t)31ULL);
v___x_1365_ = lean_usize_land(v_x_1359_, v___x_1364_);
v_j_1366_ = lean_usize_to_nat(v___x_1365_);
v___x_1367_ = lean_array_get_size(v_es_1363_);
v___x_1368_ = lean_nat_dec_lt(v_j_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec(v_j_1366_);
lean_dec(v_x_1362_);
lean_dec(v_x_1361_);
return v_x_1358_;
}
else
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1407_; 
lean_inc_ref(v_es_1363_);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_x_1358_, 0);
lean_dec(v_unused_1408_);
v___x_1370_ = v_x_1358_;
v_isShared_1371_ = v_isSharedCheck_1407_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v_x_1358_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1407_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_v_1372_; lean_object* v___x_1373_; lean_object* v_xs_x27_1374_; lean_object* v___y_1376_; 
v_v_1372_ = lean_array_fget(v_es_1363_, v_j_1366_);
v___x_1373_ = lean_box(0);
v_xs_x27_1374_ = lean_array_fset(v_es_1363_, v_j_1366_, v___x_1373_);
switch(lean_obj_tag(v_v_1372_))
{
case 0:
{
lean_object* v_key_1381_; lean_object* v_val_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1392_; 
v_key_1381_ = lean_ctor_get(v_v_1372_, 0);
v_val_1382_ = lean_ctor_get(v_v_1372_, 1);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_v_1372_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1384_ = v_v_1372_;
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_val_1382_);
lean_inc(v_key_1381_);
lean_dec(v_v_1372_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_name_eq(v_x_1361_, v_key_1381_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_del_object(v___x_1384_);
v___x_1387_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1381_, v_val_1382_, v_x_1361_, v_x_1362_);
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
v___y_1376_ = v___x_1388_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1390_; 
lean_dec(v_val_1382_);
lean_dec(v_key_1381_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v_x_1362_);
lean_ctor_set(v___x_1384_, 0, v_x_1361_);
v___x_1390_ = v___x_1384_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_x_1361_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_x_1362_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
v___y_1376_ = v___x_1390_;
goto v___jp_1375_;
}
}
}
}
case 1:
{
lean_object* v_node_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1405_; 
v_node_1393_ = lean_ctor_get(v_v_1372_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_v_1372_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1395_ = v_v_1372_;
v_isShared_1396_ = v_isSharedCheck_1405_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_node_1393_);
lean_dec(v_v_1372_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1405_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1397_ = ((size_t)5ULL);
v___x_1398_ = lean_usize_shift_right(v_x_1359_, v___x_1397_);
v___x_1399_ = ((size_t)1ULL);
v___x_1400_ = lean_usize_add(v_x_1360_, v___x_1399_);
v___x_1401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1393_, v___x_1398_, v___x_1400_, v_x_1361_, v_x_1362_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1401_);
v___x_1403_ = v___x_1395_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
v___y_1376_ = v___x_1403_;
goto v___jp_1375_;
}
}
}
default: 
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_x_1361_);
lean_ctor_set(v___x_1406_, 1, v_x_1362_);
v___y_1376_ = v___x_1406_;
goto v___jp_1375_;
}
}
v___jp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_array_fset(v_xs_x27_1374_, v_j_1366_, v___y_1376_);
lean_dec(v_j_1366_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1377_);
v___x_1379_ = v___x_1370_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
else
{
lean_object* v_ks_1409_; lean_object* v_vs_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1430_; 
v_ks_1409_ = lean_ctor_get(v_x_1358_, 0);
v_vs_1410_ = lean_ctor_get(v_x_1358_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1412_ = v_x_1358_;
v_isShared_1413_ = v_isSharedCheck_1430_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_vs_1410_);
lean_inc(v_ks_1409_);
lean_dec(v_x_1358_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1430_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_ks_1409_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_vs_1410_);
v___x_1415_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v_newNode_1416_; uint8_t v___y_1418_; size_t v___x_1424_; uint8_t v___x_1425_; 
v_newNode_1416_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1415_, v_x_1361_, v_x_1362_);
v___x_1424_ = ((size_t)7ULL);
v___x_1425_ = lean_usize_dec_le(v___x_1424_, v_x_1360_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1416_);
v___x_1427_ = lean_unsigned_to_nat(4u);
v___x_1428_ = lean_nat_dec_lt(v___x_1426_, v___x_1427_);
lean_dec(v___x_1426_);
v___y_1418_ = v___x_1428_;
goto v___jp_1417_;
}
else
{
v___y_1418_ = v___x_1425_;
goto v___jp_1417_;
}
v___jp_1417_:
{
if (v___y_1418_ == 0)
{
lean_object* v_ks_1419_; lean_object* v_vs_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_ks_1419_ = lean_ctor_get(v_newNode_1416_, 0);
lean_inc_ref(v_ks_1419_);
v_vs_1420_ = lean_ctor_get(v_newNode_1416_, 1);
lean_inc_ref(v_vs_1420_);
lean_dec_ref(v_newNode_1416_);
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1423_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1360_, v_ks_1419_, v_vs_1420_, v___x_1421_, v___x_1422_);
lean_dec_ref(v_vs_1420_);
lean_dec_ref(v_ks_1419_);
return v___x_1423_;
}
else
{
return v_newNode_1416_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1431_, lean_object* v_keys_1432_, lean_object* v_vals_1433_, lean_object* v_i_1434_, lean_object* v_entries_1435_){
_start:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_array_get_size(v_keys_1432_);
v___x_1437_ = lean_nat_dec_lt(v_i_1434_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_dec(v_i_1434_);
return v_entries_1435_;
}
else
{
lean_object* v_k_1438_; lean_object* v_v_1439_; uint64_t v___y_1441_; 
v_k_1438_ = lean_array_fget_borrowed(v_keys_1432_, v_i_1434_);
v_v_1439_ = lean_array_fget_borrowed(v_vals_1433_, v_i_1434_);
if (lean_obj_tag(v_k_1438_) == 0)
{
uint64_t v___x_1452_; 
v___x_1452_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1441_ = v___x_1452_;
goto v___jp_1440_;
}
else
{
uint64_t v_hash_1453_; 
v_hash_1453_ = lean_ctor_get_uint64(v_k_1438_, sizeof(void*)*2);
v___y_1441_ = v_hash_1453_;
goto v___jp_1440_;
}
v___jp_1440_:
{
size_t v_h_1442_; size_t v___x_1443_; lean_object* v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; size_t v_h_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_h_1442_ = lean_uint64_to_usize(v___y_1441_);
v___x_1443_ = ((size_t)5ULL);
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = ((size_t)1ULL);
v___x_1446_ = lean_usize_sub(v_depth_1431_, v___x_1445_);
v___x_1447_ = lean_usize_mul(v___x_1443_, v___x_1446_);
v_h_1448_ = lean_usize_shift_right(v_h_1442_, v___x_1447_);
v___x_1449_ = lean_nat_add(v_i_1434_, v___x_1444_);
lean_dec(v_i_1434_);
lean_inc(v_v_1439_);
lean_inc(v_k_1438_);
v___x_1450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1435_, v_h_1448_, v_depth_1431_, v_k_1438_, v_v_1439_);
v_i_1434_ = v___x_1449_;
v_entries_1435_ = v___x_1450_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1454_, lean_object* v_keys_1455_, lean_object* v_vals_1456_, lean_object* v_i_1457_, lean_object* v_entries_1458_){
_start:
{
size_t v_depth_boxed_1459_; lean_object* v_res_1460_; 
v_depth_boxed_1459_ = lean_unbox_usize(v_depth_1454_);
lean_dec(v_depth_1454_);
v_res_1460_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1459_, v_keys_1455_, v_vals_1456_, v_i_1457_, v_entries_1458_);
lean_dec_ref(v_vals_1456_);
lean_dec_ref(v_keys_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_, lean_object* v_x_1465_){
_start:
{
size_t v_x_626__boxed_1466_; size_t v_x_627__boxed_1467_; lean_object* v_res_1468_; 
v_x_626__boxed_1466_ = lean_unbox_usize(v_x_1462_);
lean_dec(v_x_1462_);
v_x_627__boxed_1467_ = lean_unbox_usize(v_x_1463_);
lean_dec(v_x_1463_);
v_res_1468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1461_, v_x_626__boxed_1466_, v_x_627__boxed_1467_, v_x_1464_, v_x_1465_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
uint64_t v___y_1473_; 
if (lean_obj_tag(v_x_1470_) == 0)
{
uint64_t v___x_1477_; 
v___x_1477_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
v___y_1473_ = v___x_1477_;
goto v___jp_1472_;
}
else
{
uint64_t v_hash_1478_; 
v_hash_1478_ = lean_ctor_get_uint64(v_x_1470_, sizeof(void*)*2);
v___y_1473_ = v_hash_1478_;
goto v___jp_1472_;
}
v___jp_1472_:
{
size_t v___x_1474_; size_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_uint64_to_usize(v___y_1473_);
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1469_, v___x_1474_, v___x_1475_, v_x_1470_, v_x_1471_);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1479_, lean_object* v_as_1480_, size_t v_i_1481_, size_t v_stop_1482_, lean_object* v_b_1483_){
_start:
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_usize_dec_eq(v_i_1481_, v_stop_1482_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; size_t v___x_1487_; size_t v___x_1488_; 
v___x_1485_ = lean_array_uget_borrowed(v_as_1480_, v_i_1481_);
lean_inc(v_declName_1479_);
lean_inc(v___x_1485_);
v___x_1486_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1483_, v___x_1485_, v_declName_1479_);
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_add(v_i_1481_, v___x_1487_);
v_i_1481_ = v___x_1488_;
v_b_1483_ = v___x_1486_;
goto _start;
}
else
{
lean_dec(v_declName_1479_);
return v_b_1483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1490_, lean_object* v_as_1491_, lean_object* v_i_1492_, lean_object* v_stop_1493_, lean_object* v_b_1494_){
_start:
{
size_t v_i_boxed_1495_; size_t v_stop_boxed_1496_; lean_object* v_res_1497_; 
v_i_boxed_1495_ = lean_unbox_usize(v_i_1492_);
lean_dec(v_i_1492_);
v_stop_boxed_1496_ = lean_unbox_usize(v_stop_1493_);
lean_dec(v_stop_1493_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1490_, v_as_1491_, v_i_boxed_1495_, v_stop_boxed_1496_, v_b_1494_);
lean_dec_ref(v_as_1491_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1498_, lean_object* v_declName_1499_, lean_object* v_s_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_array_get_size(v_eqThms_1498_);
v___x_1503_ = lean_nat_dec_lt(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_dec(v_declName_1499_);
return v_s_1500_;
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_nat_dec_le(v___x_1502_, v___x_1502_);
if (v___x_1504_ == 0)
{
if (v___x_1503_ == 0)
{
lean_dec(v_declName_1499_);
return v_s_1500_;
}
else
{
size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = ((size_t)0ULL);
v___x_1506_ = lean_usize_of_nat(v___x_1502_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1499_, v_eqThms_1498_, v___x_1505_, v___x_1506_, v_s_1500_);
return v___x_1507_;
}
}
else
{
size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = lean_usize_of_nat(v___x_1502_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1499_, v_eqThms_1498_, v___x_1508_, v___x_1509_, v_s_1500_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1511_, lean_object* v_declName_1512_, lean_object* v_s_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1511_, v_declName_1512_, v_s_1513_);
lean_dec_ref(v_eqThms_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1515_, lean_object* v_eqThms_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v_env_1520_; lean_object* v_nextMacroScope_1521_; lean_object* v_ngen_1522_; lean_object* v_auxDeclNGen_1523_; lean_object* v_traceState_1524_; lean_object* v_messages_1525_; lean_object* v_infoState_1526_; lean_object* v_snapshotTasks_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1543_; 
v___x_1519_ = lean_st_ref_take(v_a_1517_);
v_env_1520_ = lean_ctor_get(v___x_1519_, 0);
v_nextMacroScope_1521_ = lean_ctor_get(v___x_1519_, 1);
v_ngen_1522_ = lean_ctor_get(v___x_1519_, 2);
v_auxDeclNGen_1523_ = lean_ctor_get(v___x_1519_, 3);
v_traceState_1524_ = lean_ctor_get(v___x_1519_, 4);
v_messages_1525_ = lean_ctor_get(v___x_1519_, 6);
v_infoState_1526_ = lean_ctor_get(v___x_1519_, 7);
v_snapshotTasks_1527_ = lean_ctor_get(v___x_1519_, 8);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1519_, 5);
lean_dec(v_unused_1544_);
v___x_1529_ = v___x_1519_;
v_isShared_1530_ = v_isSharedCheck_1543_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_snapshotTasks_1527_);
lean_inc(v_infoState_1526_);
lean_inc(v_messages_1525_);
lean_inc(v_traceState_1524_);
lean_inc(v_auxDeclNGen_1523_);
lean_inc(v_ngen_1522_);
lean_inc(v_nextMacroScope_1521_);
lean_inc(v_env_1520_);
lean_dec(v___x_1519_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1543_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v_asyncMode_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1531_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1532_ = lean_ctor_get(v___x_1531_, 2);
v___f_1533_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1533_, 0, v_eqThms_1516_);
lean_closure_set(v___f_1533_, 1, v_declName_1515_);
v___x_1534_ = lean_box(0);
v___x_1535_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1531_, v_env_1520_, v___f_1533_, v_asyncMode_1532_, v___x_1534_);
v___x_1536_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 5, v___x_1536_);
lean_ctor_set(v___x_1529_, 0, v___x_1535_);
v___x_1538_ = v___x_1529_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_nextMacroScope_1521_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_ngen_1522_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_auxDeclNGen_1523_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_traceState_1524_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1542_, 6, v_messages_1525_);
lean_ctor_set(v_reuseFailAlloc_1542_, 7, v_infoState_1526_);
lean_ctor_set(v_reuseFailAlloc_1542_, 8, v_snapshotTasks_1527_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_st_ref_set(v_a_1517_, v___x_1538_);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1545_, lean_object* v_eqThms_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1545_, v_eqThms_1546_, v_a_1547_);
lean_dec(v_a_1547_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1550_, lean_object* v_eqThms_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1550_, v_eqThms_1551_, v_a_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1556_, lean_object* v_eqThms_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1556_, v_eqThms_1557_, v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1563_, v_x_1564_, v_x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1567_, lean_object* v_x_1568_, size_t v_x_1569_, size_t v_x_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1568_, v_x_1569_, v_x_1570_, v_x_1571_, v_x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v_x_1579_){
_start:
{
size_t v_x_895__boxed_1580_; size_t v_x_896__boxed_1581_; lean_object* v_res_1582_; 
v_x_895__boxed_1580_ = lean_unbox_usize(v_x_1576_);
lean_dec(v_x_1576_);
v_x_896__boxed_1581_ = lean_unbox_usize(v_x_1577_);
lean_dec(v_x_1577_);
v_res_1582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1574_, v_x_1575_, v_x_895__boxed_1580_, v_x_896__boxed_1581_, v_x_1578_, v_x_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1583_, lean_object* v_n_1584_, lean_object* v_k_1585_, lean_object* v_v_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1584_, v_k_1585_, v_v_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1588_, size_t v_depth_1589_, lean_object* v_keys_1590_, lean_object* v_vals_1591_, lean_object* v_heq_1592_, lean_object* v_i_1593_, lean_object* v_entries_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1589_, v_keys_1590_, v_vals_1591_, v_i_1593_, v_entries_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1596_, lean_object* v_depth_1597_, lean_object* v_keys_1598_, lean_object* v_vals_1599_, lean_object* v_heq_1600_, lean_object* v_i_1601_, lean_object* v_entries_1602_){
_start:
{
size_t v_depth_boxed_1603_; lean_object* v_res_1604_; 
v_depth_boxed_1603_ = lean_unbox_usize(v_depth_1597_);
lean_dec(v_depth_1597_);
v_res_1604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1596_, v_depth_boxed_1603_, v_keys_1598_, v_vals_1599_, v_heq_1600_, v_i_1601_, v_entries_1602_);
lean_dec_ref(v_vals_1599_);
lean_dec_ref(v_keys_1598_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1606_, v_x_1607_, v_x_1608_, v_x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1611_, lean_object* v_env_1612_, lean_object* v_idx_1613_, lean_object* v_eqs_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v_nextEq_1621_; uint8_t v___x_1622_; 
v___x_1616_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_add(v_idx_1613_, v___x_1617_);
lean_dec(v_idx_1613_);
lean_inc(v___x_1618_);
v___x_1619_ = l_Nat_reprFast(v___x_1618_);
v___x_1620_ = lean_string_append(v___x_1616_, v___x_1619_);
lean_dec_ref(v___x_1619_);
lean_inc(v_declName_1611_);
lean_inc_ref(v_env_1612_);
v_nextEq_1621_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1612_, v_declName_1611_, v___x_1620_);
v___x_1622_ = l_Lean_Environment_containsOnBranch(v_env_1612_, v_nextEq_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
lean_dec(v_nextEq_1621_);
lean_dec(v___x_1618_);
lean_dec_ref(v_env_1612_);
lean_dec(v_declName_1611_);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_eqs_1614_);
return v___x_1623_;
}
else
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_array_push(v_eqs_1614_, v_nextEq_1621_);
v_idx_1613_ = v___x_1618_;
v_eqs_1614_ = v___x_1624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1626_, lean_object* v_env_1627_, lean_object* v_idx_1628_, lean_object* v_eqs_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1626_, v_env_1627_, v_idx_1628_, v_eqs_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1632_, lean_object* v_env_1633_, lean_object* v_idx_1634_, lean_object* v_eqs_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1632_, v_env_1633_, v_idx_1634_, v_eqs_1635_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1642_, lean_object* v_env_1643_, lean_object* v_idx_1644_, lean_object* v_eqs_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1642_, v_env_1643_, v_idx_1644_, v_eqs_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; lean_object* v_env_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; uint8_t v___x_1660_; 
v___x_1655_ = lean_st_ref_get(v_a_1653_);
v_env_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc_ref_n(v_env_1656_, 3);
lean_dec(v___x_1655_);
v___x_1657_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1652_);
v___x_1658_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1656_, v_declName_1652_, v___x_1657_);
v___x_1659_ = 1;
lean_inc(v___x_1658_);
v___x_1660_ = l_Lean_Environment_contains(v_env_1656_, v___x_1658_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec(v___x_1658_);
lean_dec_ref(v_env_1656_);
lean_dec(v_declName_1652_);
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = lean_unsigned_to_nat(1u);
v___x_1664_ = lean_mk_empty_array_with_capacity(v___x_1663_);
v___x_1665_ = lean_array_push(v___x_1664_, v___x_1658_);
lean_inc(v_declName_1652_);
v___x_1666_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1652_, v_env_1656_, v___x_1663_, v___x_1665_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1676_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc_n(v_a_1667_, 2);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1652_, v_a_1667_, v_a_1653_);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v___x_1668_, 0);
lean_dec(v_unused_1677_);
v___x_1670_ = v___x_1668_;
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
else
{
lean_dec(v___x_1668_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_a_1667_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1674_ = v___x_1670_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_declName_1652_);
v_a_1678_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1666_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1666_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1686_, v_a_1687_);
lean_dec(v_a_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1690_, v_a_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1704_, lean_object* v_localInsts_1705_, lean_object* v_x_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1704_, v_localInsts_1705_, v_x_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
v_a_1721_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1712_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1712_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1729_, lean_object* v_localInsts_1730_, lean_object* v_x_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1729_, v_localInsts_1730_, v_x_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1738_, lean_object* v_lctx_1739_, lean_object* v_localInsts_1740_, lean_object* v_x_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1739_, v_localInsts_1740_, v_x_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_lctx_1749_, lean_object* v_localInsts_1750_, lean_object* v_x_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1748_, v_lctx_1749_, v_localInsts_1750_, v_x_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1761_, lean_object* v_as_x27_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
if (lean_obj_tag(v_as_x27_1762_) == 0)
{
lean_object* v___x_1769_; 
lean_dec(v_declName_1761_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_b_1763_);
return v___x_1769_;
}
else
{
lean_object* v_head_1770_; lean_object* v_tail_1771_; lean_object* v___x_1772_; 
lean_dec_ref(v_b_1763_);
v_head_1770_ = lean_ctor_get(v_as_x27_1762_, 0);
v_tail_1771_ = lean_ctor_get(v_as_x27_1762_, 1);
lean_inc(v_head_1770_);
lean_inc(v___y_1767_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v_declName_1761_);
v___x_1772_ = lean_apply_6(v_head_1770_, v_declName_1761_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, lean_box(0));
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = lean_box(0);
if (lean_obj_tag(v_a_1773_) == 1)
{
lean_object* v_val_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1785_; 
v_val_1775_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_val_1775_);
v___x_1776_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1761_, v_val_1775_, v___y_1767_);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1786_);
v___x_1778_ = v___x_1776_;
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_a_1773_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___x_1774_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1781_);
v___x_1783_ = v___x_1778_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
else
{
lean_object* v___x_1787_; 
lean_dec(v_a_1773_);
v___x_1787_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1762_ = v_tail_1771_;
v_b_1763_ = v___x_1787_;
goto _start;
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_declName_1761_);
v_a_1789_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1772_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1772_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1797_, lean_object* v_as_x27_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1797_, v_as_x27_1798_, v_b_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v_as_x27_1798_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
lean_inc(v_declName_1806_);
v___x_1812_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1850_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1850_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1850_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_unbox(v_a_1813_);
lean_dec(v_a_1813_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
lean_dec(v_declName_1806_);
v___x_1818_ = lean_box(0);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1818_);
v___x_1820_ = v___x_1815_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
else
{
lean_object* v___x_1822_; 
lean_del_object(v___x_1815_);
lean_inc(v_declName_1806_);
v___x_1822_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1806_, v___y_1810_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
if (lean_obj_tag(v_a_1823_) == 1)
{
lean_dec_ref_known(v_a_1823_, 1);
lean_dec(v_declName_1806_);
return v___x_1822_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref_known(v___x_1822_, 1);
lean_dec(v_a_1823_);
v___x_1824_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1825_ = lean_st_ref_get(v___x_1824_);
v___x_1826_ = lean_box(0);
v___x_1827_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1828_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1806_, v___x_1825_, v___x_1827_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___x_1825_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1841_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1841_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1841_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_fst_1833_; 
v_fst_1833_ = lean_ctor_get(v_a_1829_, 0);
lean_inc(v_fst_1833_);
lean_dec(v_a_1829_);
if (lean_obj_tag(v_fst_1833_) == 0)
{
lean_object* v___x_1835_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1826_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1826_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v_val_1837_; lean_object* v___x_1839_; 
v_val_1837_ = lean_ctor_get(v_fst_1833_, 0);
lean_inc(v_val_1837_);
lean_dec_ref_known(v_fst_1833_, 1);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_val_1837_);
v___x_1839_ = v___x_1831_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_val_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1828_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1828_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
else
{
lean_dec(v_declName_1806_);
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_declName_1806_);
v_a_1851_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1812_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1812_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
return v_res_1865_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1866_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1869_ = lean_box(1);
v___x_1870_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1871_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1870_);
lean_ctor_set(v___x_1872_, 2, v___x_1869_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v___f_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___f_1881_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1881_, 0, v_declName_1875_);
v___x_1882_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1884_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1882_, v___x_1883_, v___f_1881_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1892_, lean_object* v_as_1893_, lean_object* v_as_x27_1894_, lean_object* v_b_1895_, lean_object* v_a_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1892_, v_as_x27_1894_, v_b_1895_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1903_, lean_object* v_as_1904_, lean_object* v_as_x27_1905_, lean_object* v_b_1906_, lean_object* v_a_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1903_, v_as_1904_, v_as_x27_1905_, v_b_1906_, v_a_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v_as_x27_1905_);
lean_dec(v_as_1904_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1920_ = lean_unsigned_to_nat(32u);
v___x_1921_ = lean_mk_empty_array_with_capacity(v___x_1920_);
lean_dec_ref(v___x_1921_);
v___x_1922_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1923_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1914_);
v___x_1924_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1924_, 0, v_declName_1914_);
v___x_1925_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1925_, 0, lean_box(0));
lean_closure_set(v___x_1925_, 1, v_declName_1914_);
lean_closure_set(v___x_1925_, 2, v___x_1924_);
v___x_1926_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1922_, v___x_1923_, v___x_1925_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v_env_1941_; lean_object* v___x_1942_; lean_object* v_mctx_1943_; lean_object* v_lctx_1944_; lean_object* v_options_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1940_ = lean_st_ref_get(v___y_1938_);
v_env_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_env_1941_);
lean_dec(v___x_1940_);
v___x_1942_ = lean_st_ref_get(v___y_1936_);
v_mctx_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc_ref(v_mctx_1943_);
lean_dec(v___x_1942_);
v_lctx_1944_ = lean_ctor_get(v___y_1935_, 2);
v_options_1945_ = lean_ctor_get(v___y_1937_, 2);
lean_inc_ref(v_options_1945_);
lean_inc_ref(v_lctx_1944_);
v___x_1946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1946_, 0, v_env_1941_);
lean_ctor_set(v___x_1946_, 1, v_mctx_1943_);
lean_ctor_set(v___x_1946_, 2, v_lctx_1944_);
lean_ctor_set(v___x_1946_, 3, v_options_1945_);
v___x_1947_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v_msgData_1934_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1955_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1956_; double v___x_1957_; 
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_float_of_nat(v___x_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1961_, lean_object* v_msg_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_ref_1968_; lean_object* v___x_1969_; lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2014_; 
v_ref_1968_ = lean_ctor_get(v___y_1965_, 5);
v___x_1969_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2014_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2014_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v_traceState_1975_; lean_object* v_env_1976_; lean_object* v_nextMacroScope_1977_; lean_object* v_ngen_1978_; lean_object* v_auxDeclNGen_1979_; lean_object* v_cache_1980_; lean_object* v_messages_1981_; lean_object* v_infoState_1982_; lean_object* v_snapshotTasks_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2013_; 
v___x_1974_ = lean_st_ref_take(v___y_1966_);
v_traceState_1975_ = lean_ctor_get(v___x_1974_, 4);
v_env_1976_ = lean_ctor_get(v___x_1974_, 0);
v_nextMacroScope_1977_ = lean_ctor_get(v___x_1974_, 1);
v_ngen_1978_ = lean_ctor_get(v___x_1974_, 2);
v_auxDeclNGen_1979_ = lean_ctor_get(v___x_1974_, 3);
v_cache_1980_ = lean_ctor_get(v___x_1974_, 5);
v_messages_1981_ = lean_ctor_get(v___x_1974_, 6);
v_infoState_1982_ = lean_ctor_get(v___x_1974_, 7);
v_snapshotTasks_1983_ = lean_ctor_get(v___x_1974_, 8);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1985_ = v___x_1974_;
v_isShared_1986_ = v_isSharedCheck_2013_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snapshotTasks_1983_);
lean_inc(v_infoState_1982_);
lean_inc(v_messages_1981_);
lean_inc(v_cache_1980_);
lean_inc(v_traceState_1975_);
lean_inc(v_auxDeclNGen_1979_);
lean_inc(v_ngen_1978_);
lean_inc(v_nextMacroScope_1977_);
lean_inc(v_env_1976_);
lean_dec(v___x_1974_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2013_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
uint64_t v_tid_1987_; lean_object* v_traces_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2012_; 
v_tid_1987_ = lean_ctor_get_uint64(v_traceState_1975_, sizeof(void*)*1);
v_traces_1988_ = lean_ctor_get(v_traceState_1975_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_traceState_1975_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1990_ = v_traceState_1975_;
v_isShared_1991_ = v_isSharedCheck_2012_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_traces_1988_);
lean_dec(v_traceState_1975_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2012_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; double v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1992_ = lean_box(0);
v___x_1993_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_1994_ = 0;
v___x_1995_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_1996_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1996_, 0, v_cls_1961_);
lean_ctor_set(v___x_1996_, 1, v___x_1992_);
lean_ctor_set(v___x_1996_, 2, v___x_1995_);
lean_ctor_set_float(v___x_1996_, sizeof(void*)*3, v___x_1993_);
lean_ctor_set_float(v___x_1996_, sizeof(void*)*3 + 8, v___x_1993_);
lean_ctor_set_uint8(v___x_1996_, sizeof(void*)*3 + 16, v___x_1994_);
v___x_1997_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_1998_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1996_);
lean_ctor_set(v___x_1998_, 1, v_a_1970_);
lean_ctor_set(v___x_1998_, 2, v___x_1997_);
lean_inc(v_ref_1968_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_ref_1968_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = l_Lean_PersistentArray_push___redArg(v_traces_1988_, v___x_1999_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2000_);
v___x_2002_ = v___x_1990_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2000_);
lean_ctor_set_uint64(v_reuseFailAlloc_2011_, sizeof(void*)*1, v_tid_1987_);
v___x_2002_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2004_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 4, v___x_2002_);
v___x_2004_ = v___x_1985_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_env_1976_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_nextMacroScope_1977_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_ngen_1978_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_auxDeclNGen_1979_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2010_, 5, v_cache_1980_);
lean_ctor_set(v_reuseFailAlloc_2010_, 6, v_messages_1981_);
lean_ctor_set(v_reuseFailAlloc_2010_, 7, v_infoState_1982_);
lean_ctor_set(v_reuseFailAlloc_2010_, 8, v_snapshotTasks_1983_);
v___x_2004_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2005_ = lean_st_ref_set(v___y_1966_, v___x_2004_);
v___x_2006_ = lean_box(0);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_2006_);
v___x_2008_ = v___x_1972_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2015_, lean_object* v_msg_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2015_, v_msg_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2023_, lean_object* v_as_2024_, size_t v_sz_2025_, size_t v_i_2026_, lean_object* v_b_2027_){
_start:
{
lean_object* v_a_2030_; uint8_t v___x_2034_; 
v___x_2034_ = lean_usize_dec_lt(v_i_2026_, v_sz_2025_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_b_2027_);
return v___x_2035_;
}
else
{
lean_object* v_a_2036_; lean_object* v_defValue_2037_; uint8_t v___x_2038_; uint8_t v___y_2040_; 
v_a_2036_ = lean_array_uget(v_as_2024_, v_i_2026_);
v_defValue_2037_ = lean_ctor_get(v_a_2036_, 1);
v___x_2038_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2023_, v_a_2036_);
if (v___x_2038_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = lean_unbox(v_defValue_2037_);
if (v___x_2052_ == 0)
{
v___y_2040_ = v___x_2034_;
goto v___jp_2039_;
}
else
{
v___y_2040_ = v___x_2038_;
goto v___jp_2039_;
}
}
else
{
uint8_t v___x_2053_; 
v___x_2053_ = lean_unbox(v_defValue_2037_);
v___y_2040_ = v___x_2053_;
goto v___jp_2039_;
}
v___jp_2039_:
{
if (v___y_2040_ == 0)
{
lean_object* v_name_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2050_; 
v_name_2041_ = lean_ctor_get(v_a_2036_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_a_2036_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_a_2036_, 1);
lean_dec(v_unused_2051_);
v___x_2043_ = v_a_2036_;
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_name_2041_);
lean_dec(v_a_2036_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2045_, 0, v___x_2038_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v___x_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_name_2041_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_array_push(v_b_2027_, v___x_2047_);
v_a_2030_ = v___x_2048_;
goto v___jp_2029_;
}
}
}
else
{
lean_dec(v_a_2036_);
v_a_2030_ = v_b_2027_;
goto v___jp_2029_;
}
}
}
v___jp_2029_:
{
size_t v___x_2031_; size_t v___x_2032_; 
v___x_2031_ = ((size_t)1ULL);
v___x_2032_ = lean_usize_add(v_i_2026_, v___x_2031_);
v_i_2026_ = v___x_2032_;
v_b_2027_ = v_a_2030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2054_, lean_object* v_as_2055_, lean_object* v_sz_2056_, lean_object* v_i_2057_, lean_object* v_b_2058_, lean_object* v___y_2059_){
_start:
{
size_t v_sz_boxed_2060_; size_t v_i_boxed_2061_; lean_object* v_res_2062_; 
v_sz_boxed_2060_ = lean_unbox_usize(v_sz_2056_);
lean_dec(v_sz_2056_);
v_i_boxed_2061_ = lean_unbox_usize(v_i_2057_);
lean_dec(v_i_2057_);
v_res_2062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2054_, v_as_2055_, v_sz_boxed_2060_, v_i_boxed_2061_, v_b_2058_);
lean_dec_ref(v_as_2055_);
lean_dec_ref(v___x_2054_);
return v_res_2062_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2065_; size_t v_sz_2066_; 
v___x_2065_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2066_ = lean_array_size(v___x_2065_);
return v_sz_2066_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2068_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
lean_ctor_set(v___x_2068_, 2, v___x_2067_);
lean_ctor_set(v___x_2068_, 3, v___x_2067_);
lean_ctor_set(v___x_2068_, 4, v___x_2067_);
lean_ctor_set(v___x_2068_, 5, v___x_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2077_ = l_Lean_Name_append(v___x_2076_, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2080_ = l_Lean_stringToMessageData(v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_options_2087_; lean_object* v_inheritedTraceOptions_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; size_t v_sz_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v_options_2087_ = lean_ctor_get(v_a_2084_, 2);
v_inheritedTraceOptions_2088_ = lean_ctor_get(v_a_2084_, 13);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2091_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2092_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2087_, v___x_2091_, v_sz_2092_, v___x_2093_, v___x_2090_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2154_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2154_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2154_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = lean_array_get_size(v_a_2095_);
v___x_2143_ = lean_nat_dec_eq(v___x_2142_, v___x_2089_);
if (v___x_2143_ == 0)
{
uint8_t v_hasTrace_2144_; 
v_hasTrace_2144_ = lean_ctor_get_uint8(v_options_2087_, sizeof(void*)*1);
if (v_hasTrace_2144_ == 0)
{
v___y_2100_ = v_a_2083_;
v___y_2101_ = v_a_2085_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2145_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2146_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2147_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2088_, v_options_2087_, v___x_2146_);
if (v___x_2147_ == 0)
{
v___y_2100_ = v_a_2083_;
v___y_2101_ = v_a_2085_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2148_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2081_);
v___x_2149_ = l_Lean_MessageData_ofName(v_declName_2081_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2145_, v___x_2150_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_dec_ref_known(v___x_2151_, 1);
v___y_2100_ = v_a_2083_;
v___y_2101_ = v_a_2085_;
goto v___jp_2099_;
}
else
{
lean_del_object(v___x_2097_);
lean_dec(v_a_2095_);
lean_dec(v_declName_2081_);
return v___x_2151_;
}
}
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_del_object(v___x_2097_);
lean_dec(v_a_2095_);
lean_dec(v_declName_2081_);
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
v___jp_2099_:
{
lean_object* v___x_2102_; lean_object* v_env_2103_; lean_object* v_nextMacroScope_2104_; lean_object* v_ngen_2105_; lean_object* v_auxDeclNGen_2106_; lean_object* v_traceState_2107_; lean_object* v_messages_2108_; lean_object* v_infoState_2109_; lean_object* v_snapshotTasks_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2140_; 
v___x_2102_ = lean_st_ref_take(v___y_2101_);
v_env_2103_ = lean_ctor_get(v___x_2102_, 0);
v_nextMacroScope_2104_ = lean_ctor_get(v___x_2102_, 1);
v_ngen_2105_ = lean_ctor_get(v___x_2102_, 2);
v_auxDeclNGen_2106_ = lean_ctor_get(v___x_2102_, 3);
v_traceState_2107_ = lean_ctor_get(v___x_2102_, 4);
v_messages_2108_ = lean_ctor_get(v___x_2102_, 6);
v_infoState_2109_ = lean_ctor_get(v___x_2102_, 7);
v_snapshotTasks_2110_ = lean_ctor_get(v___x_2102_, 8);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v___x_2102_, 5);
lean_dec(v_unused_2141_);
v___x_2112_ = v___x_2102_;
v_isShared_2113_ = v_isSharedCheck_2140_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snapshotTasks_2110_);
lean_inc(v_infoState_2109_);
lean_inc(v_messages_2108_);
lean_inc(v_traceState_2107_);
lean_inc(v_auxDeclNGen_2106_);
lean_inc(v_ngen_2105_);
lean_inc(v_nextMacroScope_2104_);
lean_inc(v_env_2103_);
lean_dec(v___x_2102_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2140_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2114_ = l_Lean_Meta_eqnOptionsExt;
v___x_2115_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2114_, v_env_2103_, v_declName_2081_, v_a_2095_);
v___x_2116_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 5, v___x_2116_);
lean_ctor_set(v___x_2112_, 0, v___x_2115_);
v___x_2118_ = v___x_2112_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_nextMacroScope_2104_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_ngen_2105_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_auxDeclNGen_2106_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v_traceState_2107_);
lean_ctor_set(v_reuseFailAlloc_2139_, 5, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2139_, 6, v_messages_2108_);
lean_ctor_set(v_reuseFailAlloc_2139_, 7, v_infoState_2109_);
lean_ctor_set(v_reuseFailAlloc_2139_, 8, v_snapshotTasks_2110_);
v___x_2118_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v_mctx_2121_; lean_object* v_zetaDeltaFVarIds_2122_; lean_object* v_postponed_2123_; lean_object* v_diag_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2137_; 
v___x_2119_ = lean_st_ref_set(v___y_2101_, v___x_2118_);
v___x_2120_ = lean_st_ref_take(v___y_2100_);
v_mctx_2121_ = lean_ctor_get(v___x_2120_, 0);
v_zetaDeltaFVarIds_2122_ = lean_ctor_get(v___x_2120_, 2);
v_postponed_2123_ = lean_ctor_get(v___x_2120_, 3);
v_diag_2124_ = lean_ctor_get(v___x_2120_, 4);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v___x_2120_, 1);
lean_dec(v_unused_2138_);
v___x_2126_ = v___x_2120_;
v_isShared_2127_ = v_isSharedCheck_2137_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_diag_2124_);
lean_inc(v_postponed_2123_);
lean_inc(v_zetaDeltaFVarIds_2122_);
lean_inc(v_mctx_2121_);
lean_dec(v___x_2120_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2137_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 1, v___x_2128_);
v___x_2130_ = v___x_2126_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_mctx_2121_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_zetaDeltaFVarIds_2122_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_postponed_2123_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_diag_2124_);
v___x_2130_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2131_ = lean_st_ref_set(v___y_2100_, v___x_2130_);
v___x_2132_ = lean_box(0);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2132_);
v___x_2134_ = v___x_2097_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
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
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_declName_2081_);
v_a_2155_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2094_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2094_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2170_, lean_object* v_as_2171_, size_t v_sz_2172_, size_t v_i_2173_, lean_object* v_b_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2170_, v_as_2171_, v_sz_2172_, v_i_2173_, v_b_2174_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2181_, lean_object* v_as_2182_, lean_object* v_sz_2183_, lean_object* v_i_2184_, lean_object* v_b_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
size_t v_sz_boxed_2191_; size_t v_i_boxed_2192_; lean_object* v_res_2193_; 
v_sz_boxed_2191_ = lean_unbox_usize(v_sz_2183_);
lean_dec(v_sz_2183_);
v_i_boxed_2192_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_res_2193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2181_, v_as_2182_, v_sz_boxed_2191_, v_i_boxed_2192_, v_b_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_as_2182_);
lean_dec_ref(v___x_2181_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_box(0);
v___x_2196_ = lean_st_mk_ref(v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2200_){
_start:
{
uint8_t v___x_2202_; 
v___x_2202_ = l_Lean_initializing();
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref(v_f_2200_);
v___x_2203_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2205_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2206_ = lean_st_ref_take(v___x_2205_);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_f_2200_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_st_ref_set(v___x_2205_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2210_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2216_, lean_object* v_as_x27_2217_, lean_object* v_b_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
if (lean_obj_tag(v_as_x27_2217_) == 0)
{
lean_object* v___x_2224_; 
lean_dec(v_declName_2216_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_b_2218_);
return v___x_2224_;
}
else
{
lean_object* v_head_2225_; lean_object* v_tail_2226_; lean_object* v___x_2227_; 
lean_dec_ref(v_b_2218_);
v_head_2225_ = lean_ctor_get(v_as_x27_2217_, 0);
v_tail_2226_ = lean_ctor_get(v_as_x27_2217_, 1);
lean_inc(v_head_2225_);
lean_inc(v___y_2222_);
lean_inc_ref(v___y_2221_);
lean_inc(v___y_2220_);
lean_inc_ref(v___y_2219_);
lean_inc(v_declName_2216_);
v___x_2227_ = lean_apply_6(v_head_2225_, v_declName_2216_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, lean_box(0));
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2240_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2240_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2240_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_box(0);
if (lean_obj_tag(v_a_2228_) == 1)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec(v_declName_2216_);
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_a_2228_);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v___x_2232_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2234_);
v___x_2236_ = v___x_2230_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v___x_2238_; 
lean_del_object(v___x_2230_);
lean_dec(v_a_2228_);
v___x_2238_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2217_ = v_tail_2226_;
v_b_2218_ = v___x_2238_;
goto _start;
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_declName_2216_);
v_a_2241_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2227_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2227_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2249_, lean_object* v_as_x27_2250_, lean_object* v_b_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2249_, v_as_x27_2250_, v_b_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v_as_x27_2250_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2258_, lean_object* v_declName_2259_, uint8_t v_nonRec_2260_, lean_object* v___x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2270_; lean_object* v_env_2271_; uint8_t v___x_2272_; uint8_t v___x_2273_; 
v___x_2270_ = lean_st_ref_get(v___y_2265_);
v_env_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc_ref(v_env_2271_);
lean_dec(v___x_2270_);
v___x_2272_ = 1;
lean_inc(v___x_2258_);
v___x_2273_ = l_Lean_Environment_contains(v_env_2271_, v___x_2258_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_dec(v___x_2258_);
lean_inc(v_declName_2259_);
v___x_2274_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2259_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; uint8_t v___x_2276_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2276_ = lean_unbox(v_a_2275_);
lean_dec(v_a_2275_);
if (v___x_2276_ == 0)
{
lean_dec_ref(v___x_2261_);
lean_dec(v_declName_2259_);
goto v___jp_2267_;
}
else
{
lean_object* v___x_2277_; 
lean_inc(v_declName_2259_);
v___x_2277_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2259_, v___y_2265_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; uint8_t v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
v___x_2279_ = lean_unbox(v_a_2278_);
lean_dec(v_a_2278_);
if (v___x_2279_ == 0)
{
if (v_nonRec_2260_ == 0)
{
lean_dec_ref(v___x_2261_);
lean_dec(v_declName_2259_);
goto v___jp_2267_;
}
else
{
lean_object* v___x_2280_; lean_object* v_env_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2280_ = lean_st_ref_get(v___y_2265_);
v_env_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc_ref(v_env_2281_);
lean_dec(v___x_2280_);
lean_inc(v_declName_2259_);
v___x_2282_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2281_, v_declName_2259_, v___x_2261_);
v___x_2283_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2259_, v___x_2282_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2283_;
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v___x_2261_);
v___x_2284_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2285_ = lean_st_ref_get(v___x_2284_);
v___x_2286_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2287_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2259_, v___x_2285_, v___x_2286_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___x_2285_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2297_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2297_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2297_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_fst_2292_; 
v_fst_2292_ = lean_ctor_get(v_a_2288_, 0);
lean_inc(v_fst_2292_);
lean_dec(v_a_2288_);
if (lean_obj_tag(v_fst_2292_) == 0)
{
lean_del_object(v___x_2290_);
goto v___jp_2267_;
}
else
{
lean_object* v_val_2293_; lean_object* v___x_2295_; 
v_val_2293_ = lean_ctor_get(v_fst_2292_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v_fst_2292_, 1);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_val_2293_);
v___x_2295_ = v___x_2290_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_val_2293_);
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
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
v_a_2298_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2287_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2287_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v___x_2261_);
lean_dec(v_declName_2259_);
v_a_2306_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2277_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2277_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v___x_2261_);
lean_dec(v_declName_2259_);
v_a_2314_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2274_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2274_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v___x_2261_);
lean_dec(v_declName_2259_);
v___x_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2258_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
v___jp_2267_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2324_, lean_object* v_declName_2325_, lean_object* v_nonRec_2326_, lean_object* v___x_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v_nonRec_boxed_2333_; lean_object* v_res_2334_; 
v_nonRec_boxed_2333_ = lean_unbox(v_nonRec_2326_);
v_res_2334_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2324_, v_declName_2325_, v_nonRec_boxed_2333_, v___x_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_ref_2341_; lean_object* v___x_2342_; lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2351_; 
v_ref_2341_ = lean_ctor_get(v___y_2338_, 5);
v___x_2342_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
lean_inc(v_ref_2341_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v_ref_2341_);
lean_ctor_set(v___x_2347_, 1, v_a_2343_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set_tag(v___x_2345_, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2347_);
v___x_2349_ = v___x_2345_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2359_, uint8_t v_isExporting_2360_, lean_object* v___x_2361_, lean_object* v___y_2362_, lean_object* v___x_2363_, lean_object* v_a_x3f_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v_env_2367_; lean_object* v_nextMacroScope_2368_; lean_object* v_ngen_2369_; lean_object* v_auxDeclNGen_2370_; lean_object* v_traceState_2371_; lean_object* v_messages_2372_; lean_object* v_infoState_2373_; lean_object* v_snapshotTasks_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2399_; 
v___x_2366_ = lean_st_ref_take(v___y_2359_);
v_env_2367_ = lean_ctor_get(v___x_2366_, 0);
v_nextMacroScope_2368_ = lean_ctor_get(v___x_2366_, 1);
v_ngen_2369_ = lean_ctor_get(v___x_2366_, 2);
v_auxDeclNGen_2370_ = lean_ctor_get(v___x_2366_, 3);
v_traceState_2371_ = lean_ctor_get(v___x_2366_, 4);
v_messages_2372_ = lean_ctor_get(v___x_2366_, 6);
v_infoState_2373_ = lean_ctor_get(v___x_2366_, 7);
v_snapshotTasks_2374_ = lean_ctor_get(v___x_2366_, 8);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2366_, 5);
lean_dec(v_unused_2400_);
v___x_2376_ = v___x_2366_;
v_isShared_2377_ = v_isSharedCheck_2399_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_snapshotTasks_2374_);
lean_inc(v_infoState_2373_);
lean_inc(v_messages_2372_);
lean_inc(v_traceState_2371_);
lean_inc(v_auxDeclNGen_2370_);
lean_inc(v_ngen_2369_);
lean_inc(v_nextMacroScope_2368_);
lean_inc(v_env_2367_);
lean_dec(v___x_2366_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2399_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2378_ = l_Lean_Environment_setExporting(v_env_2367_, v_isExporting_2360_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 5, v___x_2361_);
lean_ctor_set(v___x_2376_, 0, v___x_2378_);
v___x_2380_ = v___x_2376_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_nextMacroScope_2368_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_ngen_2369_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_auxDeclNGen_2370_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_traceState_2371_);
lean_ctor_set(v_reuseFailAlloc_2398_, 5, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2398_, 6, v_messages_2372_);
lean_ctor_set(v_reuseFailAlloc_2398_, 7, v_infoState_2373_);
lean_ctor_set(v_reuseFailAlloc_2398_, 8, v_snapshotTasks_2374_);
v___x_2380_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v_mctx_2383_; lean_object* v_zetaDeltaFVarIds_2384_; lean_object* v_postponed_2385_; lean_object* v_diag_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2396_; 
v___x_2381_ = lean_st_ref_set(v___y_2359_, v___x_2380_);
v___x_2382_ = lean_st_ref_take(v___y_2362_);
v_mctx_2383_ = lean_ctor_get(v___x_2382_, 0);
v_zetaDeltaFVarIds_2384_ = lean_ctor_get(v___x_2382_, 2);
v_postponed_2385_ = lean_ctor_get(v___x_2382_, 3);
v_diag_2386_ = lean_ctor_get(v___x_2382_, 4);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v___x_2382_, 1);
lean_dec(v_unused_2397_);
v___x_2388_ = v___x_2382_;
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_diag_2386_);
lean_inc(v_postponed_2385_);
lean_inc(v_zetaDeltaFVarIds_2384_);
lean_inc(v_mctx_2383_);
lean_dec(v___x_2382_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 1, v___x_2363_);
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_mctx_2383_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_zetaDeltaFVarIds_2384_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_postponed_2385_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_diag_2386_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = lean_st_ref_set(v___y_2362_, v___x_2391_);
v___x_2393_ = lean_box(0);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2401_, lean_object* v_isExporting_2402_, lean_object* v___x_2403_, lean_object* v___y_2404_, lean_object* v___x_2405_, lean_object* v_a_x3f_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v_isExporting_boxed_2408_; lean_object* v_res_2409_; 
v_isExporting_boxed_2408_ = lean_unbox(v_isExporting_2402_);
v_res_2409_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2401_, v_isExporting_boxed_2408_, v___x_2403_, v___y_2404_, v___x_2405_, v_a_x3f_2406_);
lean_dec(v_a_x3f_2406_);
lean_dec(v___y_2404_);
lean_dec(v___y_2401_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2410_, uint8_t v_isExporting_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; lean_object* v_env_2418_; uint8_t v_isExporting_2419_; lean_object* v___x_2485_; uint8_t v_isModule_2486_; 
v___x_2417_ = lean_st_ref_get(v___y_2415_);
v_env_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc_ref(v_env_2418_);
lean_dec(v___x_2417_);
v_isExporting_2419_ = lean_ctor_get_uint8(v_env_2418_, sizeof(void*)*8);
v___x_2485_ = l_Lean_Environment_header(v_env_2418_);
lean_dec_ref(v_env_2418_);
v_isModule_2486_ = lean_ctor_get_uint8(v___x_2485_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2485_);
if (v_isModule_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
v___x_2487_ = lean_apply_5(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
return v___x_2487_;
}
else
{
if (v_isExporting_2419_ == 0)
{
if (v_isExporting_2411_ == 0)
{
lean_object* v___x_2488_; 
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
v___x_2488_ = lean_apply_5(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
return v___x_2488_;
}
else
{
goto v___jp_2420_;
}
}
else
{
if (v_isExporting_2411_ == 0)
{
goto v___jp_2420_;
}
else
{
lean_object* v___x_2489_; 
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
v___x_2489_ = lean_apply_5(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
return v___x_2489_;
}
}
}
v___jp_2420_:
{
lean_object* v___x_2421_; lean_object* v_env_2422_; lean_object* v_nextMacroScope_2423_; lean_object* v_ngen_2424_; lean_object* v_auxDeclNGen_2425_; lean_object* v_traceState_2426_; lean_object* v_messages_2427_; lean_object* v_infoState_2428_; lean_object* v_snapshotTasks_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2483_; 
v___x_2421_ = lean_st_ref_take(v___y_2415_);
v_env_2422_ = lean_ctor_get(v___x_2421_, 0);
v_nextMacroScope_2423_ = lean_ctor_get(v___x_2421_, 1);
v_ngen_2424_ = lean_ctor_get(v___x_2421_, 2);
v_auxDeclNGen_2425_ = lean_ctor_get(v___x_2421_, 3);
v_traceState_2426_ = lean_ctor_get(v___x_2421_, 4);
v_messages_2427_ = lean_ctor_get(v___x_2421_, 6);
v_infoState_2428_ = lean_ctor_get(v___x_2421_, 7);
v_snapshotTasks_2429_ = lean_ctor_get(v___x_2421_, 8);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2421_, 5);
lean_dec(v_unused_2484_);
v___x_2431_ = v___x_2421_;
v_isShared_2432_ = v_isSharedCheck_2483_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snapshotTasks_2429_);
lean_inc(v_infoState_2428_);
lean_inc(v_messages_2427_);
lean_inc(v_traceState_2426_);
lean_inc(v_auxDeclNGen_2425_);
lean_inc(v_ngen_2424_);
lean_inc(v_nextMacroScope_2423_);
lean_inc(v_env_2422_);
lean_dec(v___x_2421_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2483_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2433_ = l_Lean_Environment_setExporting(v_env_2422_, v_isExporting_2411_);
v___x_2434_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 5, v___x_2434_);
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2436_ = v___x_2431_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_nextMacroScope_2423_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_ngen_2424_);
lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_auxDeclNGen_2425_);
lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_traceState_2426_);
lean_ctor_set(v_reuseFailAlloc_2482_, 5, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2482_, 6, v_messages_2427_);
lean_ctor_set(v_reuseFailAlloc_2482_, 7, v_infoState_2428_);
lean_ctor_set(v_reuseFailAlloc_2482_, 8, v_snapshotTasks_2429_);
v___x_2436_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_mctx_2439_; lean_object* v_zetaDeltaFVarIds_2440_; lean_object* v_postponed_2441_; lean_object* v_diag_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2480_; 
v___x_2437_ = lean_st_ref_set(v___y_2415_, v___x_2436_);
v___x_2438_ = lean_st_ref_take(v___y_2413_);
v_mctx_2439_ = lean_ctor_get(v___x_2438_, 0);
v_zetaDeltaFVarIds_2440_ = lean_ctor_get(v___x_2438_, 2);
v_postponed_2441_ = lean_ctor_get(v___x_2438_, 3);
v_diag_2442_ = lean_ctor_get(v___x_2438_, 4);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2438_, 1);
lean_dec(v_unused_2481_);
v___x_2444_ = v___x_2438_;
v_isShared_2445_ = v_isSharedCheck_2480_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_diag_2442_);
lean_inc(v_postponed_2441_);
lean_inc(v_zetaDeltaFVarIds_2440_);
lean_inc(v_mctx_2439_);
lean_dec(v___x_2438_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2480_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_mctx_2439_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_zetaDeltaFVarIds_2440_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_postponed_2441_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_diag_2442_);
v___x_2448_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v_r_2450_; 
v___x_2449_ = lean_st_ref_set(v___y_2413_, v___x_2448_);
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
v_r_2450_ = lean_apply_5(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
if (lean_obj_tag(v_r_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2467_; 
v_a_2451_ = lean_ctor_get(v_r_2450_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_r_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2453_ = v_r_2450_;
v_isShared_2454_ = v_isSharedCheck_2467_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v_r_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2467_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
lean_inc(v_a_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set_tag(v___x_2453_, 1);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
v___x_2457_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2415_, v_isExporting_2419_, v___x_2434_, v___y_2413_, v___x_2446_, v___x_2456_);
lean_dec_ref(v___x_2456_);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2457_, 0);
lean_dec(v_unused_2465_);
v___x_2459_ = v___x_2457_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_dec(v___x_2457_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v_a_2451_);
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2451_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_a_2468_ = lean_ctor_get(v_r_2450_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v_r_2450_, 1);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2415_, v_isExporting_2419_, v___x_2434_, v___y_2413_, v___x_2446_, v___x_2469_);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2470_, 0);
lean_dec(v_unused_2478_);
v___x_2472_ = v___x_2470_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_dec(v___x_2470_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 1);
lean_ctor_set(v___x_2472_, 0, v_a_2468_);
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2468_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2490_, lean_object* v_isExporting_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v_isExporting_boxed_2497_; lean_object* v_res_2498_; 
v_isExporting_boxed_2497_ = lean_unbox(v_isExporting_2491_);
v_res_2498_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2490_, v_isExporting_boxed_2497_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2499_, uint8_t v_when_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
if (v_when_2500_ == 0)
{
lean_object* v___x_2506_; 
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
v___x_2506_ = lean_apply_5(v_x_2499_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, lean_box(0));
return v___x_2506_;
}
else
{
uint8_t v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = 0;
v___x_2508_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2499_, v___x_2507_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2509_, lean_object* v_when_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
uint8_t v_when_boxed_2516_; lean_object* v_res_2517_; 
v_when_boxed_2516_ = lean_unbox(v_when_2510_);
v_res_2517_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2509_, v_when_boxed_2516_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
return v_res_2517_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2520_ = l_Lean_stringToMessageData(v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2526_ = l_Lean_stringToMessageData(v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2527_, uint8_t v_nonRec_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v_env_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___f_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; 
v___x_2534_ = lean_st_ref_get(v___y_2532_);
v_env_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_ref(v_env_2535_);
lean_dec(v___x_2534_);
v___x_2536_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2527_);
v___x_2537_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2535_, v_declName_2527_, v___x_2536_);
v___x_2538_ = lean_box(v_nonRec_2528_);
lean_inc(v___x_2537_);
v___f_2539_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2539_, 0, v___x_2537_);
lean_closure_set(v___f_2539_, 1, v_declName_2527_);
lean_closure_set(v___f_2539_, 2, v___x_2538_);
lean_closure_set(v___f_2539_, 3, v___x_2536_);
v___x_2540_ = 1;
v___x_2541_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2539_, v___x_2540_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
if (lean_obj_tag(v_a_2542_) == 1)
{
lean_object* v_val_2543_; uint8_t v___x_2544_; 
v_val_2543_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_val_2543_);
lean_dec_ref_known(v_a_2542_, 1);
v___x_2544_ = lean_name_eq(v_val_2543_, v___x_2537_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref_known(v___x_2541_, 1);
v___x_2545_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2546_ = l_Lean_MessageData_ofName(v_val_2543_);
v___x_2547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = l_Lean_MessageData_ofName(v___x_2537_);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2553_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
lean_dec(v_val_2543_);
lean_dec(v___x_2537_);
return v___x_2541_;
}
}
else
{
lean_dec(v_a_2542_);
lean_dec(v___x_2537_);
return v___x_2541_;
}
}
else
{
lean_dec(v___x_2537_);
return v___x_2541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2563_, lean_object* v_nonRec_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
uint8_t v_nonRec_boxed_2570_; lean_object* v_res_2571_; 
v_nonRec_boxed_2570_ = lean_unbox(v_nonRec_2564_);
v_res_2571_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2563_, v_nonRec_boxed_2570_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2572_, uint8_t v_nonRec_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v___x_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2579_ = lean_box(v_nonRec_2573_);
v___f_2580_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2580_, 0, v_declName_2572_);
lean_closure_set(v___f_2580_, 1, v___x_2579_);
v___x_2581_ = lean_unsigned_to_nat(32u);
v___x_2582_ = lean_mk_empty_array_with_capacity(v___x_2581_);
lean_dec_ref(v___x_2582_);
v___x_2583_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2584_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2585_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2583_, v___x_2584_, v___f_2580_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2586_, lean_object* v_nonRec_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
uint8_t v_nonRec_boxed_2593_; lean_object* v_res_2594_; 
v_nonRec_boxed_2593_ = lean_unbox(v_nonRec_2587_);
v_res_2594_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2586_, v_nonRec_boxed_2593_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2595_, lean_object* v_as_2596_, lean_object* v_as_x27_2597_, lean_object* v_b_2598_, lean_object* v_a_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2595_, v_as_x27_2597_, v_b_2598_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2606_, lean_object* v_as_2607_, lean_object* v_as_x27_2608_, lean_object* v_b_2609_, lean_object* v_a_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2606_, v_as_2607_, v_as_x27_2608_, v_b_2609_, v_a_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v_as_x27_2608_);
lean_dec(v_as_2607_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2617_, lean_object* v_x_2618_, uint8_t v_isExporting_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2618_, v_isExporting_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2626_, lean_object* v_x_2627_, lean_object* v_isExporting_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v_isExporting_boxed_2634_; lean_object* v_res_2635_; 
v_isExporting_boxed_2634_ = lean_unbox(v_isExporting_2628_);
v_res_2635_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2626_, v_x_2627_, v_isExporting_boxed_2634_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2636_, lean_object* v_x_2637_, uint8_t v_when_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2637_, v_when_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2645_, lean_object* v_x_2646_, lean_object* v_when_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v_when_boxed_2653_; lean_object* v_res_2654_; 
v_when_boxed_2653_ = lean_unbox(v_when_2647_);
v_res_2654_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2645_, v_x_2646_, v_when_boxed_2653_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2655_, lean_object* v_msg_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2663_, lean_object* v_msg_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2663_, v_msg_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2670_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2671_ = lean_unsigned_to_nat(32u);
v___x_2672_ = lean_mk_empty_array_with_capacity(v___x_2671_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2674_ = ((size_t)5ULL);
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = lean_unsigned_to_nat(32u);
v___x_2677_ = lean_mk_empty_array_with_capacity(v___x_2676_);
v___x_2678_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2679_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
lean_ctor_set(v___x_2679_, 1, v___x_2677_);
lean_ctor_set(v___x_2679_, 2, v___x_2675_);
lean_ctor_set(v___x_2679_, 3, v___x_2675_);
lean_ctor_set_usize(v___x_2679_, 4, v___x_2674_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v_traceState_2683_; lean_object* v_traces_2684_; lean_object* v___x_2685_; lean_object* v_traceState_2686_; lean_object* v_env_2687_; lean_object* v_nextMacroScope_2688_; lean_object* v_ngen_2689_; lean_object* v_auxDeclNGen_2690_; lean_object* v_cache_2691_; lean_object* v_messages_2692_; lean_object* v_infoState_2693_; lean_object* v_snapshotTasks_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2713_; 
v___x_2682_ = lean_st_ref_get(v___y_2680_);
v_traceState_2683_ = lean_ctor_get(v___x_2682_, 4);
lean_inc_ref(v_traceState_2683_);
lean_dec(v___x_2682_);
v_traces_2684_ = lean_ctor_get(v_traceState_2683_, 0);
lean_inc_ref(v_traces_2684_);
lean_dec_ref(v_traceState_2683_);
v___x_2685_ = lean_st_ref_take(v___y_2680_);
v_traceState_2686_ = lean_ctor_get(v___x_2685_, 4);
v_env_2687_ = lean_ctor_get(v___x_2685_, 0);
v_nextMacroScope_2688_ = lean_ctor_get(v___x_2685_, 1);
v_ngen_2689_ = lean_ctor_get(v___x_2685_, 2);
v_auxDeclNGen_2690_ = lean_ctor_get(v___x_2685_, 3);
v_cache_2691_ = lean_ctor_get(v___x_2685_, 5);
v_messages_2692_ = lean_ctor_get(v___x_2685_, 6);
v_infoState_2693_ = lean_ctor_get(v___x_2685_, 7);
v_snapshotTasks_2694_ = lean_ctor_get(v___x_2685_, 8);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2696_ = v___x_2685_;
v_isShared_2697_ = v_isSharedCheck_2713_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_snapshotTasks_2694_);
lean_inc(v_infoState_2693_);
lean_inc(v_messages_2692_);
lean_inc(v_cache_2691_);
lean_inc(v_traceState_2686_);
lean_inc(v_auxDeclNGen_2690_);
lean_inc(v_ngen_2689_);
lean_inc(v_nextMacroScope_2688_);
lean_inc(v_env_2687_);
lean_dec(v___x_2685_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2713_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
uint64_t v_tid_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2711_; 
v_tid_2698_ = lean_ctor_get_uint64(v_traceState_2686_, sizeof(void*)*1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_traceState_2686_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; 
v_unused_2712_ = lean_ctor_get(v_traceState_2686_, 0);
lean_dec(v_unused_2712_);
v___x_2700_ = v_traceState_2686_;
v_isShared_2701_ = v_isSharedCheck_2711_;
goto v_resetjp_2699_;
}
else
{
lean_dec(v_traceState_2686_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2711_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2702_);
lean_ctor_set_uint64(v_reuseFailAlloc_2710_, sizeof(void*)*1, v_tid_2698_);
v___x_2704_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 4, v___x_2704_);
v___x_2706_ = v___x_2696_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_env_2687_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_nextMacroScope_2688_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_ngen_2689_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_auxDeclNGen_2690_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2709_, 5, v_cache_2691_);
lean_ctor_set(v_reuseFailAlloc_2709_, 6, v_messages_2692_);
lean_ctor_set(v_reuseFailAlloc_2709_, 7, v_infoState_2693_);
lean_ctor_set(v_reuseFailAlloc_2709_, 8, v_snapshotTasks_2694_);
v___x_2706_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_st_ref_set(v___y_2680_, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_traces_2684_);
return v___x_2708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2714_);
lean_dec(v___y_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
uint8_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2729_ = 0;
v___x_2730_ = lean_box(v___x_2729_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
return v_res_2736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2740_, lean_object* v_x_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2745_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2746_ = l_Lean_MessageData_ofName(v_name_2740_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2749_, lean_object* v_x_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2749_, v_x_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec_ref(v_x_2750_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2755_){
_start:
{
if (lean_obj_tag(v_x_2755_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v_x_2755_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_x_2755_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v_x_2755_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v_x_2755_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 1);
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v_x_2755_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_x_2755_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v_x_2755_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v_x_2755_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 0);
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2776_){
_start:
{
if (lean_obj_tag(v_e_2776_) == 0)
{
uint8_t v___x_2777_; 
v___x_2777_ = 2;
return v___x_2777_;
}
else
{
lean_object* v_a_2778_; uint8_t v___x_2779_; 
v_a_2778_ = lean_ctor_get(v_e_2776_, 0);
v___x_2779_ = lean_unbox(v_a_2778_);
if (v___x_2779_ == 0)
{
uint8_t v___x_2780_; 
v___x_2780_ = 1;
return v___x_2780_;
}
else
{
uint8_t v___x_2781_; 
v___x_2781_ = 0;
return v___x_2781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2782_){
_start:
{
uint8_t v_res_2783_; lean_object* v_r_2784_; 
v_res_2783_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2782_);
lean_dec_ref(v_e_2782_);
v_r_2784_ = lean_box(v_res_2783_);
return v_r_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2785_, size_t v_i_2786_, lean_object* v_bs_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_usize_dec_lt(v_i_2786_, v_sz_2785_);
if (v___x_2788_ == 0)
{
return v_bs_2787_;
}
else
{
lean_object* v_v_2789_; lean_object* v_msg_2790_; lean_object* v___x_2791_; lean_object* v_bs_x27_2792_; size_t v___x_2793_; size_t v___x_2794_; lean_object* v___x_2795_; 
v_v_2789_ = lean_array_uget_borrowed(v_bs_2787_, v_i_2786_);
v_msg_2790_ = lean_ctor_get(v_v_2789_, 1);
lean_inc_ref(v_msg_2790_);
v___x_2791_ = lean_unsigned_to_nat(0u);
v_bs_x27_2792_ = lean_array_uset(v_bs_2787_, v_i_2786_, v___x_2791_);
v___x_2793_ = ((size_t)1ULL);
v___x_2794_ = lean_usize_add(v_i_2786_, v___x_2793_);
v___x_2795_ = lean_array_uset(v_bs_x27_2792_, v_i_2786_, v_msg_2790_);
v_i_2786_ = v___x_2794_;
v_bs_2787_ = v___x_2795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2797_, lean_object* v_i_2798_, lean_object* v_bs_2799_){
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2797_);
lean_dec(v_sz_2797_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2798_);
lean_dec(v_i_2798_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2800_, v_i_boxed_2801_, v_bs_2799_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2803_, lean_object* v_data_2804_, lean_object* v_ref_2805_, lean_object* v_msg_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_fileName_2810_; lean_object* v_fileMap_2811_; lean_object* v_options_2812_; lean_object* v_currRecDepth_2813_; lean_object* v_maxRecDepth_2814_; lean_object* v_ref_2815_; lean_object* v_currNamespace_2816_; lean_object* v_openDecls_2817_; lean_object* v_initHeartbeats_2818_; lean_object* v_maxHeartbeats_2819_; lean_object* v_quotContext_2820_; lean_object* v_currMacroScope_2821_; uint8_t v_diag_2822_; lean_object* v_cancelTk_x3f_2823_; uint8_t v_suppressElabErrors_2824_; lean_object* v_inheritedTraceOptions_2825_; lean_object* v___x_2826_; lean_object* v_traceState_2827_; lean_object* v_traces_2828_; lean_object* v_ref_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; size_t v_sz_2832_; size_t v___x_2833_; lean_object* v___x_2834_; lean_object* v_msg_2835_; lean_object* v___x_2836_; lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2874_; 
v_fileName_2810_ = lean_ctor_get(v___y_2807_, 0);
v_fileMap_2811_ = lean_ctor_get(v___y_2807_, 1);
v_options_2812_ = lean_ctor_get(v___y_2807_, 2);
v_currRecDepth_2813_ = lean_ctor_get(v___y_2807_, 3);
v_maxRecDepth_2814_ = lean_ctor_get(v___y_2807_, 4);
v_ref_2815_ = lean_ctor_get(v___y_2807_, 5);
v_currNamespace_2816_ = lean_ctor_get(v___y_2807_, 6);
v_openDecls_2817_ = lean_ctor_get(v___y_2807_, 7);
v_initHeartbeats_2818_ = lean_ctor_get(v___y_2807_, 8);
v_maxHeartbeats_2819_ = lean_ctor_get(v___y_2807_, 9);
v_quotContext_2820_ = lean_ctor_get(v___y_2807_, 10);
v_currMacroScope_2821_ = lean_ctor_get(v___y_2807_, 11);
v_diag_2822_ = lean_ctor_get_uint8(v___y_2807_, sizeof(void*)*14);
v_cancelTk_x3f_2823_ = lean_ctor_get(v___y_2807_, 12);
v_suppressElabErrors_2824_ = lean_ctor_get_uint8(v___y_2807_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2825_ = lean_ctor_get(v___y_2807_, 13);
v___x_2826_ = lean_st_ref_get(v___y_2808_);
v_traceState_2827_ = lean_ctor_get(v___x_2826_, 4);
lean_inc_ref(v_traceState_2827_);
lean_dec(v___x_2826_);
v_traces_2828_ = lean_ctor_get(v_traceState_2827_, 0);
lean_inc_ref(v_traces_2828_);
lean_dec_ref(v_traceState_2827_);
v_ref_2829_ = l_Lean_replaceRef(v_ref_2805_, v_ref_2815_);
lean_inc_ref(v_inheritedTraceOptions_2825_);
lean_inc(v_cancelTk_x3f_2823_);
lean_inc(v_currMacroScope_2821_);
lean_inc(v_quotContext_2820_);
lean_inc(v_maxHeartbeats_2819_);
lean_inc(v_initHeartbeats_2818_);
lean_inc(v_openDecls_2817_);
lean_inc(v_currNamespace_2816_);
lean_inc(v_maxRecDepth_2814_);
lean_inc(v_currRecDepth_2813_);
lean_inc_ref(v_options_2812_);
lean_inc_ref(v_fileMap_2811_);
lean_inc_ref(v_fileName_2810_);
v___x_2830_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2830_, 0, v_fileName_2810_);
lean_ctor_set(v___x_2830_, 1, v_fileMap_2811_);
lean_ctor_set(v___x_2830_, 2, v_options_2812_);
lean_ctor_set(v___x_2830_, 3, v_currRecDepth_2813_);
lean_ctor_set(v___x_2830_, 4, v_maxRecDepth_2814_);
lean_ctor_set(v___x_2830_, 5, v_ref_2829_);
lean_ctor_set(v___x_2830_, 6, v_currNamespace_2816_);
lean_ctor_set(v___x_2830_, 7, v_openDecls_2817_);
lean_ctor_set(v___x_2830_, 8, v_initHeartbeats_2818_);
lean_ctor_set(v___x_2830_, 9, v_maxHeartbeats_2819_);
lean_ctor_set(v___x_2830_, 10, v_quotContext_2820_);
lean_ctor_set(v___x_2830_, 11, v_currMacroScope_2821_);
lean_ctor_set(v___x_2830_, 12, v_cancelTk_x3f_2823_);
lean_ctor_set(v___x_2830_, 13, v_inheritedTraceOptions_2825_);
lean_ctor_set_uint8(v___x_2830_, sizeof(void*)*14, v_diag_2822_);
lean_ctor_set_uint8(v___x_2830_, sizeof(void*)*14 + 1, v_suppressElabErrors_2824_);
v___x_2831_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2828_);
lean_dec_ref(v_traces_2828_);
v_sz_2832_ = lean_array_size(v___x_2831_);
v___x_2833_ = ((size_t)0ULL);
v___x_2834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2832_, v___x_2833_, v___x_2831_);
v_msg_2835_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2835_, 0, v_data_2804_);
lean_ctor_set(v_msg_2835_, 1, v_msg_2806_);
lean_ctor_set(v_msg_2835_, 2, v___x_2834_);
v___x_2836_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2835_, v___x_2830_, v___y_2808_);
lean_dec_ref_known(v___x_2830_, 14);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2874_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2874_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v_traceState_2842_; lean_object* v_env_2843_; lean_object* v_nextMacroScope_2844_; lean_object* v_ngen_2845_; lean_object* v_auxDeclNGen_2846_; lean_object* v_cache_2847_; lean_object* v_messages_2848_; lean_object* v_infoState_2849_; lean_object* v_snapshotTasks_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2873_; 
v___x_2841_ = lean_st_ref_take(v___y_2808_);
v_traceState_2842_ = lean_ctor_get(v___x_2841_, 4);
v_env_2843_ = lean_ctor_get(v___x_2841_, 0);
v_nextMacroScope_2844_ = lean_ctor_get(v___x_2841_, 1);
v_ngen_2845_ = lean_ctor_get(v___x_2841_, 2);
v_auxDeclNGen_2846_ = lean_ctor_get(v___x_2841_, 3);
v_cache_2847_ = lean_ctor_get(v___x_2841_, 5);
v_messages_2848_ = lean_ctor_get(v___x_2841_, 6);
v_infoState_2849_ = lean_ctor_get(v___x_2841_, 7);
v_snapshotTasks_2850_ = lean_ctor_get(v___x_2841_, 8);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2852_ = v___x_2841_;
v_isShared_2853_ = v_isSharedCheck_2873_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_snapshotTasks_2850_);
lean_inc(v_infoState_2849_);
lean_inc(v_messages_2848_);
lean_inc(v_cache_2847_);
lean_inc(v_traceState_2842_);
lean_inc(v_auxDeclNGen_2846_);
lean_inc(v_ngen_2845_);
lean_inc(v_nextMacroScope_2844_);
lean_inc(v_env_2843_);
lean_dec(v___x_2841_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2873_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
uint64_t v_tid_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2871_; 
v_tid_2854_ = lean_ctor_get_uint64(v_traceState_2842_, sizeof(void*)*1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_traceState_2842_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v_traceState_2842_, 0);
lean_dec(v_unused_2872_);
v___x_2856_ = v_traceState_2842_;
v_isShared_2857_ = v_isSharedCheck_2871_;
goto v_resetjp_2855_;
}
else
{
lean_dec(v_traceState_2842_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2871_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_ref_2805_);
lean_ctor_set(v___x_2858_, 1, v_a_2837_);
v___x_2859_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2803_, v___x_2858_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2859_);
v___x_2861_ = v___x_2856_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2859_);
lean_ctor_set_uint64(v_reuseFailAlloc_2870_, sizeof(void*)*1, v_tid_2854_);
v___x_2861_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2863_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 4, v___x_2861_);
v___x_2863_ = v___x_2852_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_env_2843_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_nextMacroScope_2844_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_ngen_2845_);
lean_ctor_set(v_reuseFailAlloc_2869_, 3, v_auxDeclNGen_2846_);
lean_ctor_set(v_reuseFailAlloc_2869_, 4, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2869_, 5, v_cache_2847_);
lean_ctor_set(v_reuseFailAlloc_2869_, 6, v_messages_2848_);
lean_ctor_set(v_reuseFailAlloc_2869_, 7, v_infoState_2849_);
lean_ctor_set(v_reuseFailAlloc_2869_, 8, v_snapshotTasks_2850_);
v___x_2863_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2864_ = lean_st_ref_set(v___y_2808_, v___x_2863_);
v___x_2865_ = lean_box(0);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2865_);
v___x_2867_ = v___x_2839_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2875_, lean_object* v_data_2876_, lean_object* v_ref_2877_, lean_object* v_msg_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2875_, v_data_2876_, v_ref_2877_, v_msg_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2882_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2885_ = l_Lean_stringToMessageData(v___x_2884_);
return v___x_2885_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2886_; double v___x_2887_; 
v___x_2886_ = lean_unsigned_to_nat(1000u);
v___x_2887_ = lean_float_of_nat(v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2888_, uint8_t v_collapsed_2889_, lean_object* v_tag_2890_, lean_object* v_opts_2891_, uint8_t v_clsEnabled_2892_, lean_object* v_oldTraces_2893_, lean_object* v_msg_2894_, lean_object* v_resStartStop_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_fst_2899_; lean_object* v_snd_2900_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v_data_2904_; lean_object* v_fst_2915_; lean_object* v_snd_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; lean_object* v___y_2920_; lean_object* v_a_2921_; uint8_t v___y_2936_; double v___y_2967_; 
v_fst_2899_ = lean_ctor_get(v_resStartStop_2895_, 0);
lean_inc(v_fst_2899_);
v_snd_2900_ = lean_ctor_get(v_resStartStop_2895_, 1);
lean_inc(v_snd_2900_);
lean_dec_ref(v_resStartStop_2895_);
v_fst_2915_ = lean_ctor_get(v_snd_2900_, 0);
lean_inc(v_fst_2915_);
v_snd_2916_ = lean_ctor_get(v_snd_2900_, 1);
lean_inc(v_snd_2916_);
lean_dec(v_snd_2900_);
v___x_2917_ = l_Lean_trace_profiler;
v___x_2918_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2891_, v___x_2917_);
if (v___x_2918_ == 0)
{
v___y_2936_ = v___x_2918_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2973_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2891_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; double v___x_2976_; double v___x_2977_; double v___x_2978_; 
v___x_2974_ = l_Lean_trace_profiler_threshold;
v___x_2975_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2891_, v___x_2974_);
v___x_2976_ = lean_float_of_nat(v___x_2975_);
v___x_2977_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_2978_ = lean_float_div(v___x_2976_, v___x_2977_);
v___y_2967_ = v___x_2978_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; double v___x_2981_; 
v___x_2979_ = l_Lean_trace_profiler_threshold;
v___x_2980_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2891_, v___x_2979_);
v___x_2981_ = lean_float_of_nat(v___x_2980_);
v___y_2967_ = v___x_2981_;
goto v___jp_2966_;
}
}
v___jp_2901_:
{
lean_object* v___x_2905_; 
lean_inc(v___y_2903_);
v___x_2905_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2893_, v_data_2904_, v___y_2903_, v___y_2902_, v___y_2896_, v___y_2897_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v___x_2906_; 
lean_dec_ref_known(v___x_2905_, 1);
v___x_2906_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2899_);
return v___x_2906_;
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_fst_2899_);
v_a_2907_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2905_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2905_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
v___jp_2919_:
{
uint8_t v_result_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; double v___x_2925_; lean_object* v_data_2926_; 
v_result_2922_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2899_);
v___x_2923_ = lean_box(v_result_2922_);
v___x_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
v___x_2925_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2890_);
lean_inc_ref(v___x_2924_);
lean_inc(v_cls_2888_);
v_data_2926_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2926_, 0, v_cls_2888_);
lean_ctor_set(v_data_2926_, 1, v___x_2924_);
lean_ctor_set(v_data_2926_, 2, v_tag_2890_);
lean_ctor_set_float(v_data_2926_, sizeof(void*)*3, v___x_2925_);
lean_ctor_set_float(v_data_2926_, sizeof(void*)*3 + 8, v___x_2925_);
lean_ctor_set_uint8(v_data_2926_, sizeof(void*)*3 + 16, v_collapsed_2889_);
if (v___x_2918_ == 0)
{
lean_dec_ref_known(v___x_2924_, 1);
lean_dec(v_snd_2916_);
lean_dec(v_fst_2915_);
lean_dec_ref(v_tag_2890_);
lean_dec(v_cls_2888_);
v___y_2902_ = v_a_2921_;
v___y_2903_ = v___y_2920_;
v_data_2904_ = v_data_2926_;
goto v___jp_2901_;
}
else
{
lean_object* v_data_2927_; double v___x_2928_; double v___x_2929_; 
lean_dec_ref_known(v_data_2926_, 3);
v_data_2927_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2927_, 0, v_cls_2888_);
lean_ctor_set(v_data_2927_, 1, v___x_2924_);
lean_ctor_set(v_data_2927_, 2, v_tag_2890_);
v___x_2928_ = lean_unbox_float(v_fst_2915_);
lean_dec(v_fst_2915_);
lean_ctor_set_float(v_data_2927_, sizeof(void*)*3, v___x_2928_);
v___x_2929_ = lean_unbox_float(v_snd_2916_);
lean_dec(v_snd_2916_);
lean_ctor_set_float(v_data_2927_, sizeof(void*)*3 + 8, v___x_2929_);
lean_ctor_set_uint8(v_data_2927_, sizeof(void*)*3 + 16, v_collapsed_2889_);
v___y_2902_ = v_a_2921_;
v___y_2903_ = v___y_2920_;
v_data_2904_ = v_data_2927_;
goto v___jp_2901_;
}
}
v___jp_2930_:
{
lean_object* v_ref_2931_; lean_object* v___x_2932_; 
v_ref_2931_ = lean_ctor_get(v___y_2896_, 5);
lean_inc(v___y_2897_);
lean_inc_ref(v___y_2896_);
lean_inc(v_fst_2899_);
v___x_2932_ = lean_apply_4(v_msg_2894_, v_fst_2899_, v___y_2896_, v___y_2897_, lean_box(0));
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v___y_2920_ = v_ref_2931_;
v_a_2921_ = v_a_2933_;
goto v___jp_2919_;
}
else
{
lean_object* v___x_2934_; 
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2920_ = v_ref_2931_;
v_a_2921_ = v___x_2934_;
goto v___jp_2919_;
}
}
v___jp_2935_:
{
if (v_clsEnabled_2892_ == 0)
{
if (v___y_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v_traceState_2938_; lean_object* v_env_2939_; lean_object* v_nextMacroScope_2940_; lean_object* v_ngen_2941_; lean_object* v_auxDeclNGen_2942_; lean_object* v_cache_2943_; lean_object* v_messages_2944_; lean_object* v_infoState_2945_; lean_object* v_snapshotTasks_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v_snd_2916_);
lean_dec(v_fst_2915_);
lean_dec_ref(v_msg_2894_);
lean_dec_ref(v_tag_2890_);
lean_dec(v_cls_2888_);
v___x_2937_ = lean_st_ref_take(v___y_2897_);
v_traceState_2938_ = lean_ctor_get(v___x_2937_, 4);
v_env_2939_ = lean_ctor_get(v___x_2937_, 0);
v_nextMacroScope_2940_ = lean_ctor_get(v___x_2937_, 1);
v_ngen_2941_ = lean_ctor_get(v___x_2937_, 2);
v_auxDeclNGen_2942_ = lean_ctor_get(v___x_2937_, 3);
v_cache_2943_ = lean_ctor_get(v___x_2937_, 5);
v_messages_2944_ = lean_ctor_get(v___x_2937_, 6);
v_infoState_2945_ = lean_ctor_get(v___x_2937_, 7);
v_snapshotTasks_2946_ = lean_ctor_get(v___x_2937_, 8);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2948_ = v___x_2937_;
v_isShared_2949_ = v_isSharedCheck_2965_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_snapshotTasks_2946_);
lean_inc(v_infoState_2945_);
lean_inc(v_messages_2944_);
lean_inc(v_cache_2943_);
lean_inc(v_traceState_2938_);
lean_inc(v_auxDeclNGen_2942_);
lean_inc(v_ngen_2941_);
lean_inc(v_nextMacroScope_2940_);
lean_inc(v_env_2939_);
lean_dec(v___x_2937_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2965_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
uint64_t v_tid_2950_; lean_object* v_traces_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2964_; 
v_tid_2950_ = lean_ctor_get_uint64(v_traceState_2938_, sizeof(void*)*1);
v_traces_2951_ = lean_ctor_get(v_traceState_2938_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_traceState_2938_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2953_ = v_traceState_2938_;
v_isShared_2954_ = v_isSharedCheck_2964_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_traces_2951_);
lean_dec(v_traceState_2938_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2964_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2955_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2893_, v_traces_2951_);
lean_dec_ref(v_traces_2951_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2955_);
v___x_2957_ = v___x_2953_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2955_);
lean_ctor_set_uint64(v_reuseFailAlloc_2963_, sizeof(void*)*1, v_tid_2950_);
v___x_2957_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2959_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 4, v___x_2957_);
v___x_2959_ = v___x_2948_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_env_2939_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_nextMacroScope_2940_);
lean_ctor_set(v_reuseFailAlloc_2962_, 2, v_ngen_2941_);
lean_ctor_set(v_reuseFailAlloc_2962_, 3, v_auxDeclNGen_2942_);
lean_ctor_set(v_reuseFailAlloc_2962_, 4, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2962_, 5, v_cache_2943_);
lean_ctor_set(v_reuseFailAlloc_2962_, 6, v_messages_2944_);
lean_ctor_set(v_reuseFailAlloc_2962_, 7, v_infoState_2945_);
lean_ctor_set(v_reuseFailAlloc_2962_, 8, v_snapshotTasks_2946_);
v___x_2959_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_st_ref_set(v___y_2897_, v___x_2959_);
v___x_2961_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2899_);
return v___x_2961_;
}
}
}
}
}
else
{
goto v___jp_2930_;
}
}
else
{
goto v___jp_2930_;
}
}
v___jp_2966_:
{
double v___x_2968_; double v___x_2969_; double v___x_2970_; uint8_t v___x_2971_; 
v___x_2968_ = lean_unbox_float(v_snd_2916_);
v___x_2969_ = lean_unbox_float(v_fst_2915_);
v___x_2970_ = lean_float_sub(v___x_2968_, v___x_2969_);
v___x_2971_ = lean_float_decLt(v___y_2967_, v___x_2970_);
v___y_2936_ = v___x_2971_;
goto v___jp_2935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_2982_, lean_object* v_collapsed_2983_, lean_object* v_tag_2984_, lean_object* v_opts_2985_, lean_object* v_clsEnabled_2986_, lean_object* v_oldTraces_2987_, lean_object* v_msg_2988_, lean_object* v_resStartStop_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
uint8_t v_collapsed_boxed_2993_; uint8_t v_clsEnabled_boxed_2994_; lean_object* v_res_2995_; 
v_collapsed_boxed_2993_ = lean_unbox(v_collapsed_2983_);
v_clsEnabled_boxed_2994_ = lean_unbox(v_clsEnabled_2986_);
v_res_2995_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_2982_, v_collapsed_boxed_2993_, v_tag_2984_, v_opts_2985_, v_clsEnabled_boxed_2994_, v_oldTraces_2987_, v_msg_2988_, v_resStartStop_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec_ref(v_opts_2985_);
return v_res_2995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2998_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3000_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
lean_ctor_set(v___x_3000_, 2, v___x_2999_);
lean_ctor_set(v___x_3000_, 3, v___x_2999_);
lean_ctor_set(v___x_3000_, 4, v___x_2998_);
lean_ctor_set(v___x_3000_, 5, v___x_2998_);
lean_ctor_set(v___x_3000_, 6, v___x_2998_);
lean_ctor_set(v___x_3000_, 7, v___x_2998_);
lean_ctor_set(v___x_3000_, 8, v___x_2998_);
lean_ctor_set(v___x_3000_, 9, v___x_2998_);
return v___x_3000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3002_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
lean_ctor_set(v___x_3002_, 2, v___x_3001_);
lean_ctor_set(v___x_3002_, 3, v___x_3001_);
lean_ctor_set(v___x_3002_, 4, v___x_3001_);
lean_ctor_set(v___x_3002_, 5, v___x_3001_);
return v___x_3002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
lean_ctor_set(v___x_3004_, 2, v___x_3003_);
lean_ctor_set(v___x_3004_, 3, v___x_3003_);
lean_ctor_set(v___x_3004_, 4, v___x_3003_);
return v___x_3004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3005_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3006_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3007_ = lean_box(1);
v___x_3008_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3009_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3008_);
lean_ctor_set(v___x_3010_, 2, v___x_3007_);
lean_ctor_set(v___x_3010_, 3, v___x_3006_);
lean_ctor_set(v___x_3010_, 4, v___x_3005_);
return v___x_3010_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3016_ = l_Lean_Name_append(v___x_3015_, v___x_3014_);
return v___x_3016_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3017_; double v___x_3018_; 
v___x_3017_ = lean_unsigned_to_nat(1000000000u);
v___x_3018_ = lean_float_of_nat(v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_3019_, lean_object* v_name_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_options_3024_; uint8_t v_hasTrace_3025_; 
v_options_3024_ = lean_ctor_get(v___y_3021_, 2);
v_hasTrace_3025_ = lean_ctor_get_uint8(v_options_3024_, sizeof(void*)*1);
if (v_hasTrace_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v_env_3027_; lean_object* v___x_3028_; 
lean_dec_ref(v___f_3019_);
v___x_3026_ = lean_st_ref_get(v___y_3022_);
v_env_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc_ref(v_env_3027_);
lean_dec(v___x_3026_);
lean_inc(v_name_3020_);
v___x_3028_ = l_Lean_Meta_declFromEqLikeName(v_env_3027_, v_name_3020_);
if (lean_obj_tag(v___x_3028_) == 1)
{
lean_object* v_val_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3128_; 
v_val_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3128_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_val_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3128_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_fst_3033_; lean_object* v_snd_3034_; lean_object* v___x_3035_; lean_object* v_env_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; 
v_fst_3033_ = lean_ctor_get(v_val_3029_, 0);
lean_inc_n(v_fst_3033_, 2);
v_snd_3034_ = lean_ctor_get(v_val_3029_, 1);
lean_inc_n(v_snd_3034_, 2);
lean_dec(v_val_3029_);
v___x_3035_ = lean_st_ref_get(v___y_3022_);
v_env_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc_ref(v_env_3036_);
lean_dec(v___x_3035_);
v___x_3037_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3036_, v_fst_3033_, v_snd_3034_);
v___x_3038_ = lean_name_eq(v_name_3020_, v___x_3037_);
lean_dec(v___x_3037_);
lean_dec(v_name_3020_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_dec(v_snd_3034_);
lean_dec(v_fst_3033_);
v___x_3039_ = lean_box(v_hasTrace_3025_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set_tag(v___x_3031_, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3039_);
v___x_3041_ = v___x_3031_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
else
{
uint8_t v___x_3043_; lean_object* v_a_3045_; 
lean_inc(v_snd_3034_);
v___x_3043_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3034_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3059_; uint8_t v___x_3060_; lean_object* v_a_3062_; 
lean_del_object(v___x_3031_);
v___x_3059_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3060_ = lean_string_dec_eq(v_snd_3034_, v___x_3059_);
lean_dec(v_snd_3034_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec(v_fst_3033_);
v___x_3074_ = lean_box(v_hasTrace_3025_);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
return v___x_3075_;
}
else
{
uint8_t v___x_3076_; uint8_t v___x_3077_; uint8_t v___x_3078_; lean_object* v___x_3079_; uint64_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3076_ = 1;
v___x_3077_ = 0;
v___x_3078_ = 2;
v___x_3079_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3079_, 0, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3079_, 1, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3079_, 2, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3079_, 3, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3079_, 4, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3079_, 5, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 6, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 7, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3079_, 8, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 9, v___x_3076_);
lean_ctor_set_uint8(v___x_3079_, 10, v___x_3077_);
lean_ctor_set_uint8(v___x_3079_, 11, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 12, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 13, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 14, v___x_3078_);
lean_ctor_set_uint8(v___x_3079_, 15, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 16, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 17, v___x_3060_);
lean_ctor_set_uint8(v___x_3079_, 18, v___x_3060_);
v___x_3080_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3079_);
v___x_3081_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set_uint64(v___x_3081_, sizeof(void*)*1, v___x_3080_);
v___x_3082_ = lean_box(1);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3085_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3087_, 0, v___x_3081_);
lean_ctor_set(v___x_3087_, 1, v___x_3082_);
lean_ctor_set(v___x_3087_, 2, v___x_3084_);
lean_ctor_set(v___x_3087_, 3, v___x_3085_);
lean_ctor_set(v___x_3087_, 4, v___x_3086_);
lean_ctor_set(v___x_3087_, 5, v___x_3083_);
lean_ctor_set(v___x_3087_, 6, v___x_3086_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*7, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*7 + 1, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*7 + 2, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*7 + 3, v___x_3038_);
v___x_3088_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3089_ = lean_st_mk_ref(v___x_3088_);
v___x_3090_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3033_, v___x_3038_, v___x_3087_, v___x_3089_, v___y_3021_, v___y_3022_);
lean_dec_ref_known(v___x_3087_, 7);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3092_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
v___x_3092_ = lean_st_ref_get(v___x_3089_);
lean_dec(v___x_3089_);
lean_dec(v___x_3092_);
v_a_3062_ = v_a_3091_;
goto v___jp_3061_;
}
else
{
lean_dec(v___x_3089_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3093_; 
v_a_3093_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3090_, 1);
v_a_3062_ = v_a_3093_;
goto v___jp_3061_;
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
v_a_3094_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3090_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3090_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
v___jp_3061_:
{
if (lean_obj_tag(v_a_3062_) == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = lean_box(v_hasTrace_3025_);
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
else
{
lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3072_; 
v_isSharedCheck_3072_ = !lean_is_exclusive(v_a_3062_);
if (v_isSharedCheck_3072_ == 0)
{
lean_object* v_unused_3073_; 
v_unused_3073_ = lean_ctor_get(v_a_3062_, 0);
lean_dec(v_unused_3073_);
v___x_3066_ = v_a_3062_;
v_isShared_3067_ = v_isSharedCheck_3072_;
goto v_resetjp_3065_;
}
else
{
lean_dec(v_a_3062_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3072_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3068_ = lean_box(v___x_3060_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set_tag(v___x_3066_, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3068_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
else
{
uint8_t v___x_3102_; uint8_t v___x_3103_; uint8_t v___x_3104_; lean_object* v___x_3105_; uint64_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec(v_snd_3034_);
v___x_3102_ = 1;
v___x_3103_ = 0;
v___x_3104_ = 2;
v___x_3105_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3105_, 0, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3105_, 1, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3105_, 2, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3105_, 3, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3105_, 4, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3105_, 5, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 6, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 7, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3105_, 8, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 9, v___x_3102_);
lean_ctor_set_uint8(v___x_3105_, 10, v___x_3103_);
lean_ctor_set_uint8(v___x_3105_, 11, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 12, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 13, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 14, v___x_3104_);
lean_ctor_set_uint8(v___x_3105_, 15, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 16, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 17, v___x_3043_);
lean_ctor_set_uint8(v___x_3105_, 18, v___x_3043_);
v___x_3106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3105_);
v___x_3107_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set_uint64(v___x_3107_, sizeof(void*)*1, v___x_3106_);
v___x_3108_ = lean_box(1);
v___x_3109_ = lean_unsigned_to_nat(0u);
v___x_3110_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3111_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3113_, 0, v___x_3107_);
lean_ctor_set(v___x_3113_, 1, v___x_3108_);
lean_ctor_set(v___x_3113_, 2, v___x_3110_);
lean_ctor_set(v___x_3113_, 3, v___x_3111_);
lean_ctor_set(v___x_3113_, 4, v___x_3112_);
lean_ctor_set(v___x_3113_, 5, v___x_3109_);
lean_ctor_set(v___x_3113_, 6, v___x_3112_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*7, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*7 + 1, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*7 + 2, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*7 + 3, v___x_3038_);
v___x_3114_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3115_ = lean_st_mk_ref(v___x_3114_);
v___x_3116_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3033_, v___x_3113_, v___x_3115_, v___y_3021_, v___y_3022_);
lean_dec_ref_known(v___x_3113_, 7);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3118_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v___x_3118_ = lean_st_ref_get(v___x_3115_);
lean_dec(v___x_3115_);
lean_dec(v___x_3118_);
v_a_3045_ = v_a_3117_;
goto v___jp_3044_;
}
else
{
lean_dec(v___x_3115_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3119_; 
v_a_3119_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3116_, 1);
v_a_3045_ = v_a_3119_;
goto v___jp_3044_;
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_del_object(v___x_3031_);
v_a_3120_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3116_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3116_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
v___jp_3044_:
{
if (lean_obj_tag(v_a_3045_) == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3046_ = lean_box(v_hasTrace_3025_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set_tag(v___x_3031_, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3046_);
v___x_3048_ = v___x_3031_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
else
{
lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3057_; 
lean_del_object(v___x_3031_);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_a_3045_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v_a_3045_, 0);
lean_dec(v_unused_3058_);
v___x_3051_ = v_a_3045_;
v_isShared_3052_ = v_isSharedCheck_3057_;
goto v_resetjp_3050_;
}
else
{
lean_dec(v_a_3045_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3057_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3053_ = lean_box(v___x_3043_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3053_);
v___x_3055_ = v___x_3051_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec(v___x_3028_);
lean_dec(v_name_3020_);
v___x_3129_ = lean_box(v_hasTrace_3025_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3131_; lean_object* v___f_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v_a_3140_; lean_object* v___y_3153_; lean_object* v___y_3154_; uint8_t v_a_3155_; lean_object* v___y_3159_; uint8_t v___y_3160_; lean_object* v___y_3161_; lean_object* v_a_3162_; lean_object* v___y_3164_; uint8_t v___y_3165_; lean_object* v___y_3166_; lean_object* v_a_3167_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v_a_3171_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v_a_3176_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v_a_3188_; lean_object* v___y_3192_; uint8_t v___y_3193_; uint8_t v___y_3194_; lean_object* v___y_3195_; lean_object* v_a_3196_; lean_object* v___y_3198_; uint8_t v___y_3199_; lean_object* v___y_3200_; lean_object* v_a_3201_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v_a_3206_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; 
v_inheritedTraceOptions_3131_ = lean_ctor_get(v___y_3021_, 13);
lean_inc(v_name_3020_);
v___f_3132_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3132_, 0, v_name_3020_);
v___x_3133_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3134_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3135_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3136_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3131_, v_options_3024_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3331_; uint8_t v___x_3332_; lean_object* v_a_3334_; lean_object* v_a_3347_; 
v___x_3331_ = l_Lean_trace_profiler;
v___x_3332_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3024_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3359_; lean_object* v_env_3360_; lean_object* v___x_3361_; 
lean_dec_ref(v___f_3132_);
lean_dec_ref(v___f_3019_);
v___x_3359_ = lean_st_ref_get(v___y_3022_);
v_env_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc_ref(v_env_3360_);
lean_dec(v___x_3359_);
lean_inc(v_name_3020_);
v___x_3361_ = l_Lean_Meta_declFromEqLikeName(v_env_3360_, v_name_3020_);
if (lean_obj_tag(v___x_3361_) == 1)
{
lean_object* v_val_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3435_; 
v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3435_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_val_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3435_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_fst_3366_; lean_object* v_snd_3367_; lean_object* v___x_3368_; lean_object* v_env_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_fst_3366_ = lean_ctor_get(v_val_3362_, 0);
lean_inc_n(v_fst_3366_, 2);
v_snd_3367_ = lean_ctor_get(v_val_3362_, 1);
lean_inc_n(v_snd_3367_, 2);
lean_dec(v_val_3362_);
v___x_3368_ = lean_st_ref_get(v___y_3022_);
v_env_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc_ref(v_env_3369_);
lean_dec(v___x_3368_);
v___x_3370_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3369_, v_fst_3366_, v_snd_3367_);
v___x_3371_ = lean_name_eq(v_name_3020_, v___x_3370_);
lean_dec(v___x_3370_);
lean_dec(v_name_3020_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
v___x_3372_ = lean_box(v___x_3332_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3372_);
v___x_3374_ = v___x_3364_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
else
{
uint8_t v___x_3376_; 
lean_inc(v_snd_3367_);
v___x_3376_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3367_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; uint8_t v___x_3378_; 
v___x_3377_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3378_ = lean_string_dec_eq(v_snd_3367_, v___x_3377_);
lean_dec(v_snd_3367_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3381_; 
lean_dec(v_fst_3366_);
v___x_3379_ = lean_box(v___x_3332_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3379_);
v___x_3381_ = v___x_3364_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
else
{
uint8_t v___x_3383_; uint8_t v___x_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; uint64_t v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_del_object(v___x_3364_);
v___x_3383_ = 1;
v___x_3384_ = 0;
v___x_3385_ = 2;
v___x_3386_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3386_, 0, v___x_3332_);
lean_ctor_set_uint8(v___x_3386_, 1, v___x_3332_);
lean_ctor_set_uint8(v___x_3386_, 2, v___x_3332_);
lean_ctor_set_uint8(v___x_3386_, 3, v___x_3332_);
lean_ctor_set_uint8(v___x_3386_, 4, v___x_3332_);
lean_ctor_set_uint8(v___x_3386_, 5, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 6, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 7, v___x_3332_);
lean_ctor_set_uint8(v___x_3386_, 8, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 9, v___x_3383_);
lean_ctor_set_uint8(v___x_3386_, 10, v___x_3384_);
lean_ctor_set_uint8(v___x_3386_, 11, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 12, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 13, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 14, v___x_3385_);
lean_ctor_set_uint8(v___x_3386_, 15, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 16, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 17, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3386_, 18, v_hasTrace_3025_);
v___x_3387_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set_uint64(v___x_3388_, sizeof(void*)*1, v___x_3387_);
v___x_3389_ = lean_box(1);
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3393_ = lean_box(0);
v___x_3394_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3394_, 0, v___x_3388_);
lean_ctor_set(v___x_3394_, 1, v___x_3389_);
lean_ctor_set(v___x_3394_, 2, v___x_3391_);
lean_ctor_set(v___x_3394_, 3, v___x_3392_);
lean_ctor_set(v___x_3394_, 4, v___x_3393_);
lean_ctor_set(v___x_3394_, 5, v___x_3390_);
lean_ctor_set(v___x_3394_, 6, v___x_3393_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*7, v___x_3332_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*7 + 1, v___x_3332_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*7 + 2, v___x_3332_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*7 + 3, v_hasTrace_3025_);
v___x_3395_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3396_ = lean_st_mk_ref(v___x_3395_);
v___x_3397_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3366_, v_hasTrace_3025_, v___x_3394_, v___x_3396_, v___y_3021_, v___y_3022_);
lean_dec_ref_known(v___x_3394_, 7);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3399_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
v___x_3399_ = lean_st_ref_get(v___x_3396_);
lean_dec(v___x_3396_);
lean_dec(v___x_3399_);
v_a_3347_ = v_a_3398_;
goto v___jp_3346_;
}
else
{
lean_dec(v___x_3396_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3400_; 
v_a_3400_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3397_, 1);
v_a_3347_ = v_a_3400_;
goto v___jp_3346_;
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
v_a_3401_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3397_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3397_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
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
else
{
uint8_t v___x_3409_; uint8_t v___x_3410_; uint8_t v___x_3411_; lean_object* v___x_3412_; uint64_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec(v_snd_3367_);
lean_del_object(v___x_3364_);
v___x_3409_ = 1;
v___x_3410_ = 0;
v___x_3411_ = 2;
v___x_3412_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3412_, 0, v___x_3332_);
lean_ctor_set_uint8(v___x_3412_, 1, v___x_3332_);
lean_ctor_set_uint8(v___x_3412_, 2, v___x_3332_);
lean_ctor_set_uint8(v___x_3412_, 3, v___x_3332_);
lean_ctor_set_uint8(v___x_3412_, 4, v___x_3332_);
lean_ctor_set_uint8(v___x_3412_, 5, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 6, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 7, v___x_3332_);
lean_ctor_set_uint8(v___x_3412_, 8, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 9, v___x_3409_);
lean_ctor_set_uint8(v___x_3412_, 10, v___x_3410_);
lean_ctor_set_uint8(v___x_3412_, 11, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 12, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 13, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 14, v___x_3411_);
lean_ctor_set_uint8(v___x_3412_, 15, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 16, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 17, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3412_, 18, v_hasTrace_3025_);
v___x_3413_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set_uint64(v___x_3414_, sizeof(void*)*1, v___x_3413_);
v___x_3415_ = lean_box(1);
v___x_3416_ = lean_unsigned_to_nat(0u);
v___x_3417_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3418_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3420_, 0, v___x_3414_);
lean_ctor_set(v___x_3420_, 1, v___x_3415_);
lean_ctor_set(v___x_3420_, 2, v___x_3417_);
lean_ctor_set(v___x_3420_, 3, v___x_3418_);
lean_ctor_set(v___x_3420_, 4, v___x_3419_);
lean_ctor_set(v___x_3420_, 5, v___x_3416_);
lean_ctor_set(v___x_3420_, 6, v___x_3419_);
lean_ctor_set_uint8(v___x_3420_, sizeof(void*)*7, v___x_3332_);
lean_ctor_set_uint8(v___x_3420_, sizeof(void*)*7 + 1, v___x_3332_);
lean_ctor_set_uint8(v___x_3420_, sizeof(void*)*7 + 2, v___x_3332_);
lean_ctor_set_uint8(v___x_3420_, sizeof(void*)*7 + 3, v_hasTrace_3025_);
v___x_3421_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3422_ = lean_st_mk_ref(v___x_3421_);
v___x_3423_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3366_, v___x_3420_, v___x_3422_, v___y_3021_, v___y_3022_);
lean_dec_ref_known(v___x_3420_, 7);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = lean_st_ref_get(v___x_3422_);
lean_dec(v___x_3422_);
lean_dec(v___x_3425_);
v_a_3334_ = v_a_3424_;
goto v___jp_3333_;
}
else
{
lean_dec(v___x_3422_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3426_; 
v_a_3426_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3423_, 1);
v_a_3334_ = v_a_3426_;
goto v___jp_3333_;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
v_a_3427_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3423_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3423_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
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
lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec(v___x_3361_);
lean_dec(v_name_3020_);
v___x_3436_ = lean_box(v___x_3332_);
v___x_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
}
else
{
goto v___jp_3215_;
}
v___jp_3333_:
{
if (lean_obj_tag(v_a_3334_) == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_box(v___x_3332_);
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
return v___x_3336_;
}
else
{
lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3344_; 
v_isSharedCheck_3344_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; 
v_unused_3345_ = lean_ctor_get(v_a_3334_, 0);
lean_dec(v_unused_3345_);
v___x_3338_ = v_a_3334_;
v_isShared_3339_ = v_isSharedCheck_3344_;
goto v_resetjp_3337_;
}
else
{
lean_dec(v_a_3334_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3344_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = lean_box(v_hasTrace_3025_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set_tag(v___x_3338_, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3340_);
v___x_3342_ = v___x_3338_;
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
}
}
v___jp_3346_:
{
if (lean_obj_tag(v_a_3347_) == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = lean_box(v___x_3332_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
return v___x_3349_;
}
else
{
lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3357_; 
v_isSharedCheck_3357_ = !lean_is_exclusive(v_a_3347_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v_a_3347_, 0);
lean_dec(v_unused_3358_);
v___x_3351_ = v_a_3347_;
v_isShared_3352_ = v_isSharedCheck_3357_;
goto v_resetjp_3350_;
}
else
{
lean_dec(v_a_3347_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3357_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3353_ = lean_box(v_hasTrace_3025_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3353_);
v___x_3355_ = v___x_3351_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
else
{
goto v___jp_3215_;
}
v___jp_3137_:
{
lean_object* v___x_3141_; double v___x_3142_; double v___x_3143_; double v___x_3144_; double v___x_3145_; double v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3141_ = lean_io_mono_nanos_now();
v___x_3142_ = lean_float_of_nat(v___y_3138_);
v___x_3143_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3144_ = lean_float_div(v___x_3142_, v___x_3143_);
v___x_3145_ = lean_float_of_nat(v___x_3141_);
v___x_3146_ = lean_float_div(v___x_3145_, v___x_3143_);
v___x_3147_ = lean_box_float(v___x_3144_);
v___x_3148_ = lean_box_float(v___x_3146_);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3147_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_a_3140_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3133_, v_hasTrace_3025_, v___x_3134_, v_options_3024_, v___x_3136_, v___y_3139_, v___f_3132_, v___x_3150_, v___y_3021_, v___y_3022_);
return v___x_3151_;
}
v___jp_3152_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_box(v_a_3155_);
v___x_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
v___y_3138_ = v___y_3153_;
v___y_3139_ = v___y_3154_;
v_a_3140_ = v___x_3157_;
goto v___jp_3137_;
}
v___jp_3158_:
{
if (lean_obj_tag(v_a_3162_) == 0)
{
v___y_3153_ = v___y_3159_;
v___y_3154_ = v___y_3161_;
v_a_3155_ = v___y_3160_;
goto v___jp_3152_;
}
else
{
lean_dec_ref_known(v_a_3162_, 1);
v___y_3153_ = v___y_3159_;
v___y_3154_ = v___y_3161_;
v_a_3155_ = v_hasTrace_3025_;
goto v___jp_3152_;
}
}
v___jp_3163_:
{
if (lean_obj_tag(v_a_3167_) == 0)
{
v___y_3153_ = v___y_3164_;
v___y_3154_ = v___y_3166_;
v_a_3155_ = v___y_3165_;
goto v___jp_3152_;
}
else
{
lean_dec_ref_known(v_a_3167_, 1);
v___y_3153_ = v___y_3164_;
v___y_3154_ = v___y_3166_;
v_a_3155_ = v_hasTrace_3025_;
goto v___jp_3152_;
}
}
v___jp_3168_:
{
lean_object* v___x_3172_; 
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v_a_3171_);
v___y_3138_ = v___y_3169_;
v___y_3139_ = v___y_3170_;
v_a_3140_ = v___x_3172_;
goto v___jp_3137_;
}
v___jp_3173_:
{
lean_object* v___x_3177_; double v___x_3178_; double v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3177_ = lean_io_get_num_heartbeats();
v___x_3178_ = lean_float_of_nat(v___y_3174_);
v___x_3179_ = lean_float_of_nat(v___x_3177_);
v___x_3180_ = lean_box_float(v___x_3178_);
v___x_3181_ = lean_box_float(v___x_3179_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3180_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_a_3176_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3133_, v_hasTrace_3025_, v___x_3134_, v_options_3024_, v___x_3136_, v___y_3175_, v___f_3132_, v___x_3183_, v___y_3021_, v___y_3022_);
return v___x_3184_;
}
v___jp_3185_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_box(v_a_3188_);
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
v___y_3174_ = v___y_3186_;
v___y_3175_ = v___y_3187_;
v_a_3176_ = v___x_3190_;
goto v___jp_3173_;
}
v___jp_3191_:
{
if (lean_obj_tag(v_a_3196_) == 0)
{
v___y_3186_ = v___y_3192_;
v___y_3187_ = v___y_3195_;
v_a_3188_ = v___y_3193_;
goto v___jp_3185_;
}
else
{
lean_dec_ref_known(v_a_3196_, 1);
v___y_3186_ = v___y_3192_;
v___y_3187_ = v___y_3195_;
v_a_3188_ = v___y_3194_;
goto v___jp_3185_;
}
}
v___jp_3197_:
{
if (lean_obj_tag(v_a_3201_) == 0)
{
uint8_t v___x_3202_; 
v___x_3202_ = 0;
v___y_3186_ = v___y_3198_;
v___y_3187_ = v___y_3200_;
v_a_3188_ = v___x_3202_;
goto v___jp_3185_;
}
else
{
lean_dec_ref_known(v_a_3201_, 1);
v___y_3186_ = v___y_3198_;
v___y_3187_ = v___y_3200_;
v_a_3188_ = v___y_3199_;
goto v___jp_3185_;
}
}
v___jp_3203_:
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_a_3206_);
v___y_3174_ = v___y_3204_;
v___y_3175_ = v___y_3205_;
v_a_3176_ = v___x_3207_;
goto v___jp_3173_;
}
v___jp_3208_:
{
if (lean_obj_tag(v___y_3211_) == 0)
{
lean_object* v_a_3212_; uint8_t v___x_3213_; 
v_a_3212_ = lean_ctor_get(v___y_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___y_3211_, 1);
v___x_3213_ = lean_unbox(v_a_3212_);
lean_dec(v_a_3212_);
v___y_3186_ = v___y_3209_;
v___y_3187_ = v___y_3210_;
v_a_3188_ = v___x_3213_;
goto v___jp_3185_;
}
else
{
lean_object* v_a_3214_; 
v_a_3214_ = lean_ctor_get(v___y_3211_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___y_3211_, 1);
v___y_3204_ = v___y_3209_;
v___y_3205_ = v___y_3210_;
v_a_3206_ = v_a_3214_;
goto v___jp_3203_;
}
}
v___jp_3215_:
{
lean_object* v___x_3216_; lean_object* v_a_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3216_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3022_);
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref(v___x_3216_);
v___x_3218_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3219_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3024_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v_env_3222_; lean_object* v___x_3223_; 
lean_dec_ref(v___f_3019_);
v___x_3220_ = lean_io_mono_nanos_now();
v___x_3221_ = lean_st_ref_get(v___y_3022_);
v_env_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc_ref(v_env_3222_);
lean_dec(v___x_3221_);
lean_inc(v_name_3020_);
v___x_3223_ = l_Lean_Meta_declFromEqLikeName(v_env_3222_, v_name_3020_);
if (lean_obj_tag(v___x_3223_) == 1)
{
lean_object* v_val_3224_; lean_object* v_fst_3225_; lean_object* v_snd_3226_; lean_object* v___x_3227_; lean_object* v_env_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v_val_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_val_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v_fst_3225_ = lean_ctor_get(v_val_3224_, 0);
lean_inc_n(v_fst_3225_, 2);
v_snd_3226_ = lean_ctor_get(v_val_3224_, 1);
lean_inc_n(v_snd_3226_, 2);
lean_dec(v_val_3224_);
v___x_3227_ = lean_st_ref_get(v___y_3022_);
v_env_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc_ref(v_env_3228_);
lean_dec(v___x_3227_);
v___x_3229_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3228_, v_fst_3225_, v_snd_3226_);
v___x_3230_ = lean_name_eq(v_name_3020_, v___x_3229_);
lean_dec(v___x_3229_);
lean_dec(v_name_3020_);
if (v___x_3230_ == 0)
{
lean_dec(v_snd_3226_);
lean_dec(v_fst_3225_);
v___y_3153_ = v___x_3220_;
v___y_3154_ = v_a_3217_;
v_a_3155_ = v___x_3219_;
goto v___jp_3152_;
}
else
{
uint8_t v___x_3231_; 
lean_inc(v_snd_3226_);
v___x_3231_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3226_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3232_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3233_ = lean_string_dec_eq(v_snd_3226_, v___x_3232_);
lean_dec(v_snd_3226_);
if (v___x_3233_ == 0)
{
lean_dec(v_fst_3225_);
v___y_3153_ = v___x_3220_;
v___y_3154_ = v_a_3217_;
v_a_3155_ = v___x_3219_;
goto v___jp_3152_;
}
else
{
uint8_t v___x_3234_; uint8_t v___x_3235_; uint8_t v___x_3236_; lean_object* v___x_3237_; uint64_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3234_ = 1;
v___x_3235_ = 0;
v___x_3236_ = 2;
v___x_3237_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3237_, 0, v___x_3219_);
lean_ctor_set_uint8(v___x_3237_, 1, v___x_3219_);
lean_ctor_set_uint8(v___x_3237_, 2, v___x_3219_);
lean_ctor_set_uint8(v___x_3237_, 3, v___x_3219_);
lean_ctor_set_uint8(v___x_3237_, 4, v___x_3219_);
lean_ctor_set_uint8(v___x_3237_, 5, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 6, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 7, v___x_3219_);
lean_ctor_set_uint8(v___x_3237_, 8, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 9, v___x_3234_);
lean_ctor_set_uint8(v___x_3237_, 10, v___x_3235_);
lean_ctor_set_uint8(v___x_3237_, 11, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 12, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 13, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 14, v___x_3236_);
lean_ctor_set_uint8(v___x_3237_, 15, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 16, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 17, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3237_, 18, v_hasTrace_3025_);
v___x_3238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3237_);
v___x_3239_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3239_, 0, v___x_3237_);
lean_ctor_set_uint64(v___x_3239_, sizeof(void*)*1, v___x_3238_);
v___x_3240_ = lean_box(1);
v___x_3241_ = lean_unsigned_to_nat(0u);
v___x_3242_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3243_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3244_ = lean_box(0);
v___x_3245_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3245_, 0, v___x_3239_);
lean_ctor_set(v___x_3245_, 1, v___x_3240_);
lean_ctor_set(v___x_3245_, 2, v___x_3242_);
lean_ctor_set(v___x_3245_, 3, v___x_3243_);
lean_ctor_set(v___x_3245_, 4, v___x_3244_);
lean_ctor_set(v___x_3245_, 5, v___x_3241_);
lean_ctor_set(v___x_3245_, 6, v___x_3244_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*7, v___x_3219_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*7 + 1, v___x_3219_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*7 + 2, v___x_3219_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*7 + 3, v_hasTrace_3025_);
v___x_3246_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3247_ = lean_st_mk_ref(v___x_3246_);
v___x_3248_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3225_, v_hasTrace_3025_, v___x_3245_, v___x_3247_, v___y_3021_, v___y_3022_);
lean_dec_ref_known(v___x_3245_, 7);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = lean_st_ref_get(v___x_3247_);
lean_dec(v___x_3247_);
lean_dec(v___x_3250_);
v___y_3164_ = v___x_3220_;
v___y_3165_ = v___x_3219_;
v___y_3166_ = v_a_3217_;
v_a_3167_ = v_a_3249_;
goto v___jp_3163_;
}
else
{
lean_dec(v___x_3247_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3248_, 1);
v___y_3164_ = v___x_3220_;
v___y_3165_ = v___x_3219_;
v___y_3166_ = v_a_3217_;
v_a_3167_ = v_a_3251_;
goto v___jp_3163_;
}
else
{
lean_object* v_a_3252_; 
v_a_3252_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3248_, 1);
v___y_3169_ = v___x_3220_;
v___y_3170_ = v_a_3217_;
v_a_3171_ = v_a_3252_;
goto v___jp_3168_;
}
}
}
}
else
{
uint8_t v___x_3253_; uint8_t v___x_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; uint64_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_dec(v_snd_3226_);
v___x_3253_ = 1;
v___x_3254_ = 0;
v___x_3255_ = 2;
v___x_3256_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3256_, 0, v___x_3219_);
lean_ctor_set_uint8(v___x_3256_, 1, v___x_3219_);
lean_ctor_set_uint8(v___x_3256_, 2, v___x_3219_);
lean_ctor_set_uint8(v___x_3256_, 3, v___x_3219_);
lean_ctor_set_uint8(v___x_3256_, 4, v___x_3219_);
lean_ctor_set_uint8(v___x_3256_, 5, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 6, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 7, v___x_3219_);
lean_ctor_set_uint8(v___x_3256_, 8, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 9, v___x_3253_);
lean_ctor_set_uint8(v___x_3256_, 10, v___x_3254_);
lean_ctor_set_uint8(v___x_3256_, 11, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 12, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 13, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 14, v___x_3255_);
lean_ctor_set_uint8(v___x_3256_, 15, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 16, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 17, v_hasTrace_3025_);
lean_ctor_set_uint8(v___x_3256_, 18, v_hasTrace_3025_);
v___x_3257_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3256_);
v___x_3258_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set_uint64(v___x_3258_, sizeof(void*)*1, v___x_3257_);
v___x_3259_ = lean_box(1);
v___x_3260_ = lean_unsigned_to_nat(0u);
v___x_3261_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3262_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3263_ = lean_box(0);
v___x_3264_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3264_, 0, v___x_3258_);
lean_ctor_set(v___x_3264_, 1, v___x_3259_);
lean_ctor_set(v___x_3264_, 2, v___x_3261_);
lean_ctor_set(v___x_3264_, 3, v___x_3262_);
lean_ctor_set(v___x_3264_, 4, v___x_3263_);
lean_ctor_set(v___x_3264_, 5, v___x_3260_);
lean_ctor_set(v___x_3264_, 6, v___x_3263_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7, v___x_3219_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 1, v___x_3219_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 2, v___x_3219_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 3, v_hasTrace_3025_);
v___x_3265_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3266_ = lean_st_mk_ref(v___x_3265_);
v___x_3267_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3225_, v___x_3264_, v___x_3266_, v___y_3021_, v___y_3022_);
lean_dec_ref_known(v___x_3264_, 7);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3269_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3267_, 1);
v___x_3269_ = lean_st_ref_get(v___x_3266_);
lean_dec(v___x_3266_);
lean_dec(v___x_3269_);
v___y_3159_ = v___x_3220_;
v___y_3160_ = v___x_3219_;
v___y_3161_ = v_a_3217_;
v_a_3162_ = v_a_3268_;
goto v___jp_3158_;
}
else
{
lean_dec(v___x_3266_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3267_, 1);
v___y_3159_ = v___x_3220_;
v___y_3160_ = v___x_3219_;
v___y_3161_ = v_a_3217_;
v_a_3162_ = v_a_3270_;
goto v___jp_3158_;
}
else
{
lean_object* v_a_3271_; 
v_a_3271_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3267_, 1);
v___y_3169_ = v___x_3220_;
v___y_3170_ = v_a_3217_;
v_a_3171_ = v_a_3271_;
goto v___jp_3168_;
}
}
}
}
}
else
{
lean_dec(v___x_3223_);
lean_dec(v_name_3020_);
v___y_3153_ = v___x_3220_;
v___y_3154_ = v_a_3217_;
v_a_3155_ = v___x_3219_;
goto v___jp_3152_;
}
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v_env_3274_; lean_object* v___x_3275_; 
v___x_3272_ = lean_io_get_num_heartbeats();
v___x_3273_ = lean_st_ref_get(v___y_3022_);
v_env_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc_ref(v_env_3274_);
lean_dec(v___x_3273_);
lean_inc(v_name_3020_);
v___x_3275_ = l_Lean_Meta_declFromEqLikeName(v_env_3274_, v_name_3020_);
if (lean_obj_tag(v___x_3275_) == 1)
{
lean_object* v_val_3276_; lean_object* v_fst_3277_; lean_object* v_snd_3278_; lean_object* v___x_3279_; lean_object* v_env_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v_val_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_val_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v_fst_3277_ = lean_ctor_get(v_val_3276_, 0);
lean_inc_n(v_fst_3277_, 2);
v_snd_3278_ = lean_ctor_get(v_val_3276_, 1);
lean_inc_n(v_snd_3278_, 2);
lean_dec(v_val_3276_);
v___x_3279_ = lean_st_ref_get(v___y_3022_);
v_env_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc_ref(v_env_3280_);
lean_dec(v___x_3279_);
v___x_3281_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3280_, v_fst_3277_, v_snd_3278_);
v___x_3282_ = lean_name_eq(v_name_3020_, v___x_3281_);
lean_dec(v___x_3281_);
lean_dec(v_name_3020_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec(v_snd_3278_);
lean_dec(v_fst_3277_);
v___x_3283_ = lean_box(0);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3021_);
v___x_3284_ = lean_apply_4(v___f_3019_, v___x_3283_, v___y_3021_, v___y_3022_, lean_box(0));
v___y_3209_ = v___x_3272_;
v___y_3210_ = v_a_3217_;
v___y_3211_ = v___x_3284_;
goto v___jp_3208_;
}
else
{
uint8_t v___x_3285_; 
lean_inc(v_snd_3278_);
v___x_3285_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3278_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3286_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3287_ = lean_string_dec_eq(v_snd_3278_, v___x_3286_);
lean_dec(v_snd_3278_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_dec(v_fst_3277_);
v___x_3288_ = lean_box(0);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3021_);
v___x_3289_ = lean_apply_4(v___f_3019_, v___x_3288_, v___y_3021_, v___y_3022_, lean_box(0));
v___y_3209_ = v___x_3272_;
v___y_3210_ = v_a_3217_;
v___y_3211_ = v___x_3289_;
goto v___jp_3208_;
}
else
{
uint8_t v___x_3290_; uint8_t v___x_3291_; uint8_t v___x_3292_; lean_object* v___x_3293_; uint64_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec_ref(v___f_3019_);
v___x_3290_ = 1;
v___x_3291_ = 0;
v___x_3292_ = 2;
v___x_3293_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3293_, 0, v___x_3285_);
lean_ctor_set_uint8(v___x_3293_, 1, v___x_3285_);
lean_ctor_set_uint8(v___x_3293_, 2, v___x_3285_);
lean_ctor_set_uint8(v___x_3293_, 3, v___x_3285_);
lean_ctor_set_uint8(v___x_3293_, 4, v___x_3285_);
lean_ctor_set_uint8(v___x_3293_, 5, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 6, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 7, v___x_3285_);
lean_ctor_set_uint8(v___x_3293_, 8, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 9, v___x_3290_);
lean_ctor_set_uint8(v___x_3293_, 10, v___x_3291_);
lean_ctor_set_uint8(v___x_3293_, 11, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 12, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 13, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 14, v___x_3292_);
lean_ctor_set_uint8(v___x_3293_, 15, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 16, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 17, v___x_3219_);
lean_ctor_set_uint8(v___x_3293_, 18, v___x_3219_);
v___x_3294_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3293_);
v___x_3295_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set_uint64(v___x_3295_, sizeof(void*)*1, v___x_3294_);
v___x_3296_ = lean_box(1);
v___x_3297_ = lean_unsigned_to_nat(0u);
v___x_3298_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3299_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3301_, 0, v___x_3295_);
lean_ctor_set(v___x_3301_, 1, v___x_3296_);
lean_ctor_set(v___x_3301_, 2, v___x_3298_);
lean_ctor_set(v___x_3301_, 3, v___x_3299_);
lean_ctor_set(v___x_3301_, 4, v___x_3300_);
lean_ctor_set(v___x_3301_, 5, v___x_3297_);
lean_ctor_set(v___x_3301_, 6, v___x_3300_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*7, v___x_3285_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*7 + 1, v___x_3285_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*7 + 2, v___x_3285_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*7 + 3, v___x_3219_);
v___x_3302_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3303_ = lean_st_mk_ref(v___x_3302_);
v___x_3304_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3277_, v___x_3219_, v___x_3301_, v___x_3303_, v___y_3021_, v___y_3022_);
lean_dec_ref_known(v___x_3301_, 7);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = lean_st_ref_get(v___x_3303_);
lean_dec(v___x_3303_);
lean_dec(v___x_3306_);
v___y_3192_ = v___x_3272_;
v___y_3193_ = v___x_3285_;
v___y_3194_ = v___x_3219_;
v___y_3195_ = v_a_3217_;
v_a_3196_ = v_a_3305_;
goto v___jp_3191_;
}
else
{
lean_dec(v___x_3303_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3307_; 
v_a_3307_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3304_, 1);
v___y_3192_ = v___x_3272_;
v___y_3193_ = v___x_3285_;
v___y_3194_ = v___x_3219_;
v___y_3195_ = v_a_3217_;
v_a_3196_ = v_a_3307_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3308_; 
v_a_3308_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3304_, 1);
v___y_3204_ = v___x_3272_;
v___y_3205_ = v_a_3217_;
v_a_3206_ = v_a_3308_;
goto v___jp_3203_;
}
}
}
}
else
{
uint8_t v___x_3309_; uint8_t v___x_3310_; uint8_t v___x_3311_; uint8_t v___x_3312_; lean_object* v___x_3313_; uint64_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec(v_snd_3278_);
lean_dec_ref(v___f_3019_);
v___x_3309_ = 0;
v___x_3310_ = 1;
v___x_3311_ = 0;
v___x_3312_ = 2;
v___x_3313_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_3313_, 0, v___x_3309_);
lean_ctor_set_uint8(v___x_3313_, 1, v___x_3309_);
lean_ctor_set_uint8(v___x_3313_, 2, v___x_3309_);
lean_ctor_set_uint8(v___x_3313_, 3, v___x_3309_);
lean_ctor_set_uint8(v___x_3313_, 4, v___x_3309_);
lean_ctor_set_uint8(v___x_3313_, 5, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 6, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 7, v___x_3309_);
lean_ctor_set_uint8(v___x_3313_, 8, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 9, v___x_3310_);
lean_ctor_set_uint8(v___x_3313_, 10, v___x_3311_);
lean_ctor_set_uint8(v___x_3313_, 11, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 12, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 13, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 14, v___x_3312_);
lean_ctor_set_uint8(v___x_3313_, 15, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 16, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 17, v___x_3219_);
lean_ctor_set_uint8(v___x_3313_, 18, v___x_3219_);
v___x_3314_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3313_);
v___x_3315_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set_uint64(v___x_3315_, sizeof(void*)*1, v___x_3314_);
v___x_3316_ = lean_box(1);
v___x_3317_ = lean_unsigned_to_nat(0u);
v___x_3318_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3321_, 0, v___x_3315_);
lean_ctor_set(v___x_3321_, 1, v___x_3316_);
lean_ctor_set(v___x_3321_, 2, v___x_3318_);
lean_ctor_set(v___x_3321_, 3, v___x_3319_);
lean_ctor_set(v___x_3321_, 4, v___x_3320_);
lean_ctor_set(v___x_3321_, 5, v___x_3317_);
lean_ctor_set(v___x_3321_, 6, v___x_3320_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*7, v___x_3309_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*7 + 1, v___x_3309_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*7 + 2, v___x_3309_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*7 + 3, v___x_3219_);
v___x_3322_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3323_ = lean_st_mk_ref(v___x_3322_);
v___x_3324_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3277_, v___x_3321_, v___x_3323_, v___y_3021_, v___y_3022_);
lean_dec_ref_known(v___x_3321_, 7);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
v___x_3326_ = lean_st_ref_get(v___x_3323_);
lean_dec(v___x_3323_);
lean_dec(v___x_3326_);
v___y_3198_ = v___x_3272_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v_a_3217_;
v_a_3201_ = v_a_3325_;
goto v___jp_3197_;
}
else
{
lean_dec(v___x_3323_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3324_, 1);
v___y_3198_ = v___x_3272_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v_a_3217_;
v_a_3201_ = v_a_3327_;
goto v___jp_3197_;
}
else
{
lean_object* v_a_3328_; 
v_a_3328_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3324_, 1);
v___y_3204_ = v___x_3272_;
v___y_3205_ = v_a_3217_;
v_a_3206_ = v_a_3328_;
goto v___jp_3203_;
}
}
}
}
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec(v___x_3275_);
lean_dec(v_name_3020_);
v___x_3329_ = lean_box(0);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3021_);
v___x_3330_ = lean_apply_4(v___f_3019_, v___x_3329_, v___y_3021_, v___y_3022_, lean_box(0));
v___y_3209_ = v___x_3272_;
v___y_3210_ = v_a_3217_;
v___y_3211_ = v___x_3330_;
goto v___jp_3208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3438_, lean_object* v_name_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3438_, v_name_3439_, v___y_3440_, v___y_3441_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
return v_res_3443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3487_ = lean_unsigned_to_nat(3137104340u);
v___x_3488_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3489_ = l_Lean_Name_num___override(v___x_3488_, v___x_3487_);
return v___x_3489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3491_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3492_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3493_ = l_Lean_Name_str___override(v___x_3492_, v___x_3491_);
return v___x_3493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3496_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3497_ = l_Lean_Name_str___override(v___x_3496_, v___x_3495_);
return v___x_3497_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_unsigned_to_nat(2u);
v___x_3499_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3500_ = l_Lean_Name_num___override(v___x_3499_, v___x_3498_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3502_; lean_object* v___x_3503_; 
v___f_3502_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3503_ = l_Lean_registerReservedNameAction(v___f_3502_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_dec_ref_known(v___x_3503_, 1);
v___x_3504_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3505_ = 0;
v___x_3506_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3507_ = l_Lean_registerTraceClass(v___x_3504_, v___x_3505_, v___x_3506_);
return v___x_3507_;
}
else
{
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3510_, lean_object* v_x_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3511_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3516_, lean_object* v_x_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3516_, v_x_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
return v_res_3521_;
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
