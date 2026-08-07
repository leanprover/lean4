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
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v_fileName_675_; lean_object* v_fileMap_676_; lean_object* v_currRecDepth_677_; lean_object* v_ref_678_; lean_object* v_currNamespace_679_; lean_object* v_openDecls_680_; lean_object* v_initHeartbeats_681_; lean_object* v_maxHeartbeats_682_; lean_object* v_quotContext_683_; lean_object* v_currMacroScope_684_; lean_object* v_cancelTk_x3f_685_; uint8_t v_suppressElabErrors_686_; lean_object* v_inheritedTraceOptions_687_; lean_object* v___y_688_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_env_695_; lean_object* v___x_696_; lean_object* v_toEnvExtension_697_; lean_object* v_asyncMode_698_; lean_object* v_fileName_699_; lean_object* v_fileMap_700_; lean_object* v_options_701_; lean_object* v_currRecDepth_702_; lean_object* v_ref_703_; lean_object* v_currNamespace_704_; lean_object* v_openDecls_705_; lean_object* v_initHeartbeats_706_; lean_object* v_maxHeartbeats_707_; lean_object* v_quotContext_708_; lean_object* v_currMacroScope_709_; lean_object* v_cancelTk_x3f_710_; uint8_t v_suppressElabErrors_711_; lean_object* v_inheritedTraceOptions_712_; uint8_t v___y_714_; lean_object* v___y_715_; uint8_t v___y_716_; lean_object* v___y_738_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; 
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
v___x_690_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_674_, v___x_689_);
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
lean_ctor_set(v___x_691_, 2, v___y_674_);
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
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*14, v___y_673_);
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
v___x_729_ = l_Lean_Kernel_enableDiag(v_env_718_, v___y_714_);
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
v___y_673_ = v___x_741_;
v___y_674_ = v___y_738_;
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
v___y_714_ = v___x_741_;
v___y_715_ = v___y_738_;
v___y_716_ = v___x_742_;
goto v___jp_713_;
}
}
else
{
v___y_714_ = v___x_741_;
v___y_715_ = v___y_738_;
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
size_t v_x_338__boxed_1133_; lean_object* v_res_1134_; 
v_x_338__boxed_1133_ = lean_unbox_usize(v_x_1131_);
lean_dec(v_x_1131_);
v_res_1134_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1130_, v_x_338__boxed_1133_, v_x_1132_);
lean_dec(v_x_1132_);
lean_dec_ref(v_x_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
uint64_t v___y_1138_; 
if (lean_obj_tag(v_x_1136_) == 0)
{
uint64_t v___x_1141_; 
v___x_1141_ = 1723ULL;
v___y_1138_ = v___x_1141_;
goto v___jp_1137_;
}
else
{
uint64_t v_hash_1142_; 
v_hash_1142_ = lean_ctor_get_uint64(v_x_1136_, sizeof(void*)*2);
v___y_1138_ = v_hash_1142_;
goto v___jp_1137_;
}
v___jp_1137_:
{
size_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_uint64_to_usize(v___y_1138_);
v___x_1140_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1135_, v___x_1139_, v_x_1136_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1143_, v_x_1144_);
lean_dec(v_x_1144_);
lean_dec_ref(v_x_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v_env_1150_; lean_object* v___x_1151_; lean_object* v_asyncMode_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1149_ = lean_st_ref_get(v_a_1147_);
v_env_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_env_1150_);
lean_dec(v___x_1149_);
v___x_1151_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1152_ = lean_ctor_get(v___x_1151_, 2);
v___x_1153_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1154_ = lean_box(0);
v___x_1155_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1153_, v___x_1151_, v_env_1150_, v_asyncMode_1152_, v___x_1154_);
v___x_1156_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1155_, v_thmName_1146_);
lean_dec(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec(v_thmName_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1162_, v_a_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_thmName_1167_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1173_, v_x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1176_, v_x_1177_, v_x_1178_);
lean_dec(v_x_1178_);
lean_dec_ref(v_x_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1180_, lean_object* v_x_1181_, size_t v_x_1182_, lean_object* v_x_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1181_, v_x_1182_, v_x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
size_t v_x_431__boxed_1189_; lean_object* v_res_1190_; 
v_x_431__boxed_1189_ = lean_unbox_usize(v_x_1187_);
lean_dec(v_x_1187_);
v_res_1190_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1185_, v_x_1186_, v_x_431__boxed_1189_, v_x_1188_);
lean_dec(v_x_1188_);
lean_dec_ref(v_x_1186_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1191_, lean_object* v_keys_1192_, lean_object* v_vals_1193_, lean_object* v_heq_1194_, lean_object* v_i_1195_, lean_object* v_k_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1192_, v_vals_1193_, v_i_1195_, v_k_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1198_, lean_object* v_keys_1199_, lean_object* v_vals_1200_, lean_object* v_heq_1201_, lean_object* v_i_1202_, lean_object* v_k_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1198_, v_keys_1199_, v_vals_1200_, v_heq_1201_, v_i_1202_, v_k_1203_);
lean_dec(v_k_1203_);
lean_dec_ref(v_vals_1200_);
lean_dec_ref(v_keys_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1205_, lean_object* v_i_1206_, lean_object* v_k_1207_){
_start:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_array_get_size(v_keys_1205_);
v___x_1209_ = lean_nat_dec_lt(v_i_1206_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_dec(v_i_1206_);
return v___x_1209_;
}
else
{
lean_object* v_k_x27_1210_; uint8_t v___x_1211_; 
v_k_x27_1210_ = lean_array_fget_borrowed(v_keys_1205_, v_i_1206_);
v___x_1211_ = lean_name_eq(v_k_1207_, v_k_x27_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_add(v_i_1206_, v___x_1212_);
lean_dec(v_i_1206_);
v_i_1206_ = v___x_1213_;
goto _start;
}
else
{
lean_dec(v_i_1206_);
return v___x_1211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1215_, lean_object* v_i_1216_, lean_object* v_k_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1215_, v_i_1216_, v_k_1217_);
lean_dec(v_k_1217_);
lean_dec_ref(v_keys_1215_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1220_, size_t v_x_1221_, lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 0)
{
lean_object* v_es_1223_; lean_object* v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; lean_object* v_j_1227_; lean_object* v___x_1228_; 
v_es_1223_ = lean_ctor_get(v_x_1220_, 0);
v___x_1224_ = lean_box(2);
v___x_1225_ = ((size_t)31ULL);
v___x_1226_ = lean_usize_land(v_x_1221_, v___x_1225_);
v_j_1227_ = lean_usize_to_nat(v___x_1226_);
v___x_1228_ = lean_array_get_borrowed(v___x_1224_, v_es_1223_, v_j_1227_);
lean_dec(v_j_1227_);
switch(lean_obj_tag(v___x_1228_))
{
case 0:
{
lean_object* v_key_1229_; uint8_t v___x_1230_; 
v_key_1229_ = lean_ctor_get(v___x_1228_, 0);
v___x_1230_ = lean_name_eq(v_x_1222_, v_key_1229_);
return v___x_1230_;
}
case 1:
{
lean_object* v_node_1231_; size_t v___x_1232_; size_t v___x_1233_; 
v_node_1231_ = lean_ctor_get(v___x_1228_, 0);
v___x_1232_ = ((size_t)5ULL);
v___x_1233_ = lean_usize_shift_right(v_x_1221_, v___x_1232_);
v_x_1220_ = v_node_1231_;
v_x_1221_ = v___x_1233_;
goto _start;
}
default: 
{
uint8_t v___x_1235_; 
v___x_1235_ = 0;
return v___x_1235_;
}
}
}
else
{
lean_object* v_ks_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_ks_1236_ = lean_ctor_get(v_x_1220_, 0);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1236_, v___x_1237_, v_x_1222_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
size_t v_x_324__boxed_1242_; uint8_t v_res_1243_; lean_object* v_r_1244_; 
v_x_324__boxed_1242_ = lean_unbox_usize(v_x_1240_);
lean_dec(v_x_1240_);
v_res_1243_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1239_, v_x_324__boxed_1242_, v_x_1241_);
lean_dec(v_x_1241_);
lean_dec_ref(v_x_1239_);
v_r_1244_ = lean_box(v_res_1243_);
return v_r_1244_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
uint64_t v___y_1248_; 
if (lean_obj_tag(v_x_1246_) == 0)
{
uint64_t v___x_1251_; 
v___x_1251_ = 1723ULL;
v___y_1248_ = v___x_1251_;
goto v___jp_1247_;
}
else
{
uint64_t v_hash_1252_; 
v_hash_1252_ = lean_ctor_get_uint64(v_x_1246_, sizeof(void*)*2);
v___y_1248_ = v_hash_1252_;
goto v___jp_1247_;
}
v___jp_1247_:
{
size_t v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = lean_uint64_to_usize(v___y_1248_);
v___x_1250_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1245_, v___x_1249_, v_x_1246_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1253_, v_x_1254_);
lean_dec(v_x_1254_);
lean_dec_ref(v_x_1253_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v_env_1261_; lean_object* v___x_1262_; lean_object* v_asyncMode_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1260_ = lean_st_ref_get(v_a_1258_);
v_env_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref(v_env_1261_);
lean_dec(v___x_1260_);
v___x_1262_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1263_ = lean_ctor_get(v___x_1262_, 2);
v___x_1264_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1265_ = lean_box(0);
v___x_1266_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1264_, v___x_1262_, v_env_1261_, v_asyncMode_1263_, v___x_1265_);
v___x_1267_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1266_, v_thmName_1257_);
lean_dec(v___x_1266_);
v___x_1268_ = lean_box(v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec(v_thmName_1270_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1274_, v_a_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Meta_isEqnThm(v_thmName_1279_, v_a_1280_, v_a_1281_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_thmName_1279_);
return v_res_1283_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1285_, v_x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1288_, v_x_1289_, v_x_1290_);
lean_dec(v_x_1290_);
lean_dec_ref(v_x_1289_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1293_, lean_object* v_x_1294_, size_t v_x_1295_, lean_object* v_x_1296_){
_start:
{
uint8_t v___x_1297_; 
v___x_1297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1294_, v_x_1295_, v_x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
size_t v_x_413__boxed_1302_; uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_x_413__boxed_1302_ = lean_unbox_usize(v_x_1300_);
lean_dec(v_x_1300_);
v_res_1303_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1298_, v_x_1299_, v_x_413__boxed_1302_, v_x_1301_);
lean_dec(v_x_1301_);
lean_dec_ref(v_x_1299_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1305_, lean_object* v_keys_1306_, lean_object* v_vals_1307_, lean_object* v_heq_1308_, lean_object* v_i_1309_, lean_object* v_k_1310_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1306_, v_i_1309_, v_k_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1312_, lean_object* v_keys_1313_, lean_object* v_vals_1314_, lean_object* v_heq_1315_, lean_object* v_i_1316_, lean_object* v_k_1317_){
_start:
{
uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_res_1318_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1312_, v_keys_1313_, v_vals_1314_, v_heq_1315_, v_i_1316_, v_k_1317_);
lean_dec(v_k_1317_);
lean_dec_ref(v_vals_1314_);
lean_dec_ref(v_keys_1313_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_){
_start:
{
lean_object* v_ks_1324_; lean_object* v_vs_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1349_; 
v_ks_1324_ = lean_ctor_get(v_x_1320_, 0);
v_vs_1325_ = lean_ctor_get(v_x_1320_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_x_1320_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1327_ = v_x_1320_;
v_isShared_1328_ = v_isSharedCheck_1349_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_vs_1325_);
lean_inc(v_ks_1324_);
lean_dec(v_x_1320_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1349_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_array_get_size(v_ks_1324_);
v___x_1330_ = lean_nat_dec_lt(v_x_1321_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
lean_dec(v_x_1321_);
v___x_1331_ = lean_array_push(v_ks_1324_, v_x_1322_);
v___x_1332_ = lean_array_push(v_vs_1325_, v_x_1323_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___x_1332_);
lean_ctor_set(v___x_1327_, 0, v___x_1331_);
v___x_1334_ = v___x_1327_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v_k_x27_1336_; uint8_t v___x_1337_; 
v_k_x27_1336_ = lean_array_fget_borrowed(v_ks_1324_, v_x_1321_);
v___x_1337_ = lean_name_eq(v_x_1322_, v_k_x27_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1339_; 
if (v_isShared_1328_ == 0)
{
v___x_1339_ = v___x_1327_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_ks_1324_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_vs_1325_);
v___x_1339_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_unsigned_to_nat(1u);
v___x_1341_ = lean_nat_add(v_x_1321_, v___x_1340_);
lean_dec(v_x_1321_);
v_x_1320_ = v___x_1339_;
v_x_1321_ = v___x_1341_;
goto _start;
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1344_ = lean_array_fset(v_ks_1324_, v_x_1321_, v_x_1322_);
v___x_1345_ = lean_array_fset(v_vs_1325_, v_x_1321_, v_x_1323_);
lean_dec(v_x_1321_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___x_1345_);
lean_ctor_set(v___x_1327_, 0, v___x_1344_);
v___x_1347_ = v___x_1327_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1350_, lean_object* v_k_1351_, lean_object* v_v_1352_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1350_, v___x_1353_, v_k_1351_, v_v_1352_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1356_, size_t v_x_1357_, size_t v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 0)
{
lean_object* v_es_1361_; size_t v___x_1362_; size_t v___x_1363_; lean_object* v_j_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_es_1361_ = lean_ctor_get(v_x_1356_, 0);
v___x_1362_ = ((size_t)31ULL);
v___x_1363_ = lean_usize_land(v_x_1357_, v___x_1362_);
v_j_1364_ = lean_usize_to_nat(v___x_1363_);
v___x_1365_ = lean_array_get_size(v_es_1361_);
v___x_1366_ = lean_nat_dec_lt(v_j_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_dec(v_j_1364_);
lean_dec(v_x_1360_);
lean_dec(v_x_1359_);
return v_x_1356_;
}
else
{
lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1405_; 
lean_inc_ref(v_es_1361_);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_x_1356_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v_x_1356_, 0);
lean_dec(v_unused_1406_);
v___x_1368_ = v_x_1356_;
v_isShared_1369_ = v_isSharedCheck_1405_;
goto v_resetjp_1367_;
}
else
{
lean_dec(v_x_1356_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1405_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_v_1370_; lean_object* v___x_1371_; lean_object* v_xs_x27_1372_; lean_object* v___y_1374_; 
v_v_1370_ = lean_array_fget(v_es_1361_, v_j_1364_);
v___x_1371_ = lean_box(0);
v_xs_x27_1372_ = lean_array_fset(v_es_1361_, v_j_1364_, v___x_1371_);
switch(lean_obj_tag(v_v_1370_))
{
case 0:
{
lean_object* v_key_1379_; lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1390_; 
v_key_1379_ = lean_ctor_get(v_v_1370_, 0);
v_val_1380_ = lean_ctor_get(v_v_1370_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_v_1370_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1382_ = v_v_1370_;
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_inc(v_key_1379_);
lean_dec(v_v_1370_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_name_eq(v_x_1359_, v_key_1379_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_del_object(v___x_1382_);
v___x_1385_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1379_, v_val_1380_, v_x_1359_, v_x_1360_);
v___x_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
v___y_1374_ = v___x_1386_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1388_; 
lean_dec(v_val_1380_);
lean_dec(v_key_1379_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v_x_1360_);
lean_ctor_set(v___x_1382_, 0, v_x_1359_);
v___x_1388_ = v___x_1382_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_x_1359_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_x_1360_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v___y_1374_ = v___x_1388_;
goto v___jp_1373_;
}
}
}
}
case 1:
{
lean_object* v_node_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1403_; 
v_node_1391_ = lean_ctor_get(v_v_1370_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_v_1370_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1393_ = v_v_1370_;
v_isShared_1394_ = v_isSharedCheck_1403_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_node_1391_);
lean_dec(v_v_1370_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1403_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
size_t v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1395_ = ((size_t)5ULL);
v___x_1396_ = lean_usize_shift_right(v_x_1357_, v___x_1395_);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_add(v_x_1358_, v___x_1397_);
v___x_1399_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1391_, v___x_1396_, v___x_1398_, v_x_1359_, v_x_1360_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1399_);
v___x_1401_ = v___x_1393_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
v___y_1374_ = v___x_1401_;
goto v___jp_1373_;
}
}
}
default: 
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_x_1359_);
lean_ctor_set(v___x_1404_, 1, v_x_1360_);
v___y_1374_ = v___x_1404_;
goto v___jp_1373_;
}
}
v___jp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_array_fset(v_xs_x27_1372_, v_j_1364_, v___y_1374_);
lean_dec(v_j_1364_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1375_);
v___x_1377_ = v___x_1368_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
else
{
lean_object* v_ks_1407_; lean_object* v_vs_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1428_; 
v_ks_1407_ = lean_ctor_get(v_x_1356_, 0);
v_vs_1408_ = lean_ctor_get(v_x_1356_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_x_1356_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1410_ = v_x_1356_;
v_isShared_1411_ = v_isSharedCheck_1428_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_vs_1408_);
lean_inc(v_ks_1407_);
lean_dec(v_x_1356_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1428_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_ks_1407_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_vs_1408_);
v___x_1413_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v_newNode_1414_; uint8_t v___y_1416_; size_t v___x_1422_; uint8_t v___x_1423_; 
v_newNode_1414_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1413_, v_x_1359_, v_x_1360_);
v___x_1422_ = ((size_t)7ULL);
v___x_1423_ = lean_usize_dec_le(v___x_1422_, v_x_1358_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1424_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1414_);
v___x_1425_ = lean_unsigned_to_nat(4u);
v___x_1426_ = lean_nat_dec_lt(v___x_1424_, v___x_1425_);
lean_dec(v___x_1424_);
v___y_1416_ = v___x_1426_;
goto v___jp_1415_;
}
else
{
v___y_1416_ = v___x_1423_;
goto v___jp_1415_;
}
v___jp_1415_:
{
if (v___y_1416_ == 0)
{
lean_object* v_ks_1417_; lean_object* v_vs_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_ks_1417_ = lean_ctor_get(v_newNode_1414_, 0);
lean_inc_ref(v_ks_1417_);
v_vs_1418_ = lean_ctor_get(v_newNode_1414_, 1);
lean_inc_ref(v_vs_1418_);
lean_dec_ref(v_newNode_1414_);
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1421_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1358_, v_ks_1417_, v_vs_1418_, v___x_1419_, v___x_1420_);
lean_dec_ref(v_vs_1418_);
lean_dec_ref(v_ks_1417_);
return v___x_1421_;
}
else
{
return v_newNode_1414_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1429_, lean_object* v_keys_1430_, lean_object* v_vals_1431_, lean_object* v_i_1432_, lean_object* v_entries_1433_){
_start:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_array_get_size(v_keys_1430_);
v___x_1435_ = lean_nat_dec_lt(v_i_1432_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_dec(v_i_1432_);
return v_entries_1433_;
}
else
{
lean_object* v_k_1436_; lean_object* v_v_1437_; uint64_t v___y_1439_; 
v_k_1436_ = lean_array_fget_borrowed(v_keys_1430_, v_i_1432_);
v_v_1437_ = lean_array_fget_borrowed(v_vals_1431_, v_i_1432_);
if (lean_obj_tag(v_k_1436_) == 0)
{
uint64_t v___x_1450_; 
v___x_1450_ = 1723ULL;
v___y_1439_ = v___x_1450_;
goto v___jp_1438_;
}
else
{
uint64_t v_hash_1451_; 
v_hash_1451_ = lean_ctor_get_uint64(v_k_1436_, sizeof(void*)*2);
v___y_1439_ = v_hash_1451_;
goto v___jp_1438_;
}
v___jp_1438_:
{
size_t v_h_1440_; size_t v___x_1441_; lean_object* v___x_1442_; size_t v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; size_t v_h_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_h_1440_ = lean_uint64_to_usize(v___y_1439_);
v___x_1441_ = ((size_t)5ULL);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = ((size_t)1ULL);
v___x_1444_ = lean_usize_sub(v_depth_1429_, v___x_1443_);
v___x_1445_ = lean_usize_mul(v___x_1441_, v___x_1444_);
v_h_1446_ = lean_usize_shift_right(v_h_1440_, v___x_1445_);
v___x_1447_ = lean_nat_add(v_i_1432_, v___x_1442_);
lean_dec(v_i_1432_);
lean_inc(v_v_1437_);
lean_inc(v_k_1436_);
v___x_1448_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1433_, v_h_1446_, v_depth_1429_, v_k_1436_, v_v_1437_);
v_i_1432_ = v___x_1447_;
v_entries_1433_ = v___x_1448_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1452_, lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_i_1455_, lean_object* v_entries_1456_){
_start:
{
size_t v_depth_boxed_1457_; lean_object* v_res_1458_; 
v_depth_boxed_1457_ = lean_unbox_usize(v_depth_1452_);
lean_dec(v_depth_1452_);
v_res_1458_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1457_, v_keys_1453_, v_vals_1454_, v_i_1455_, v_entries_1456_);
lean_dec_ref(v_vals_1454_);
lean_dec_ref(v_keys_1453_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
size_t v_x_621__boxed_1464_; size_t v_x_622__boxed_1465_; lean_object* v_res_1466_; 
v_x_621__boxed_1464_ = lean_unbox_usize(v_x_1460_);
lean_dec(v_x_1460_);
v_x_622__boxed_1465_ = lean_unbox_usize(v_x_1461_);
lean_dec(v_x_1461_);
v_res_1466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1459_, v_x_621__boxed_1464_, v_x_622__boxed_1465_, v_x_1462_, v_x_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
uint64_t v___y_1471_; 
if (lean_obj_tag(v_x_1468_) == 0)
{
uint64_t v___x_1475_; 
v___x_1475_ = 1723ULL;
v___y_1471_ = v___x_1475_;
goto v___jp_1470_;
}
else
{
uint64_t v_hash_1476_; 
v_hash_1476_ = lean_ctor_get_uint64(v_x_1468_, sizeof(void*)*2);
v___y_1471_ = v_hash_1476_;
goto v___jp_1470_;
}
v___jp_1470_:
{
size_t v___x_1472_; size_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_uint64_to_usize(v___y_1471_);
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1467_, v___x_1472_, v___x_1473_, v_x_1468_, v_x_1469_);
return v___x_1474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1477_, lean_object* v_as_1478_, size_t v_i_1479_, size_t v_stop_1480_, lean_object* v_b_1481_){
_start:
{
uint8_t v___x_1482_; 
v___x_1482_ = lean_usize_dec_eq(v_i_1479_, v_stop_1480_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; size_t v___x_1485_; size_t v___x_1486_; 
v___x_1483_ = lean_array_uget_borrowed(v_as_1478_, v_i_1479_);
lean_inc(v_declName_1477_);
lean_inc(v___x_1483_);
v___x_1484_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1481_, v___x_1483_, v_declName_1477_);
v___x_1485_ = ((size_t)1ULL);
v___x_1486_ = lean_usize_add(v_i_1479_, v___x_1485_);
v_i_1479_ = v___x_1486_;
v_b_1481_ = v___x_1484_;
goto _start;
}
else
{
lean_dec(v_declName_1477_);
return v_b_1481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1488_, lean_object* v_as_1489_, lean_object* v_i_1490_, lean_object* v_stop_1491_, lean_object* v_b_1492_){
_start:
{
size_t v_i_boxed_1493_; size_t v_stop_boxed_1494_; lean_object* v_res_1495_; 
v_i_boxed_1493_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_stop_boxed_1494_ = lean_unbox_usize(v_stop_1491_);
lean_dec(v_stop_1491_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1488_, v_as_1489_, v_i_boxed_1493_, v_stop_boxed_1494_, v_b_1492_);
lean_dec_ref(v_as_1489_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1496_, lean_object* v_declName_1497_, lean_object* v_s_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_array_get_size(v_eqThms_1496_);
v___x_1501_ = lean_nat_dec_lt(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_dec(v_declName_1497_);
return v_s_1498_;
}
else
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_nat_dec_le(v___x_1500_, v___x_1500_);
if (v___x_1502_ == 0)
{
if (v___x_1501_ == 0)
{
lean_dec(v_declName_1497_);
return v_s_1498_;
}
else
{
size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = ((size_t)0ULL);
v___x_1504_ = lean_usize_of_nat(v___x_1500_);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1497_, v_eqThms_1496_, v___x_1503_, v___x_1504_, v_s_1498_);
return v___x_1505_;
}
}
else
{
size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = lean_usize_of_nat(v___x_1500_);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1497_, v_eqThms_1496_, v___x_1506_, v___x_1507_, v_s_1498_);
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1509_, lean_object* v_declName_1510_, lean_object* v_s_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1509_, v_declName_1510_, v_s_1511_);
lean_dec_ref(v_eqThms_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1513_, lean_object* v_eqThms_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v_env_1518_; lean_object* v_nextMacroScope_1519_; lean_object* v_ngen_1520_; lean_object* v_auxDeclNGen_1521_; lean_object* v_traceState_1522_; lean_object* v_messages_1523_; lean_object* v_infoState_1524_; lean_object* v_snapshotTasks_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1541_; 
v___x_1517_ = lean_st_ref_take(v_a_1515_);
v_env_1518_ = lean_ctor_get(v___x_1517_, 0);
v_nextMacroScope_1519_ = lean_ctor_get(v___x_1517_, 1);
v_ngen_1520_ = lean_ctor_get(v___x_1517_, 2);
v_auxDeclNGen_1521_ = lean_ctor_get(v___x_1517_, 3);
v_traceState_1522_ = lean_ctor_get(v___x_1517_, 4);
v_messages_1523_ = lean_ctor_get(v___x_1517_, 6);
v_infoState_1524_ = lean_ctor_get(v___x_1517_, 7);
v_snapshotTasks_1525_ = lean_ctor_get(v___x_1517_, 8);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1517_, 5);
lean_dec(v_unused_1542_);
v___x_1527_ = v___x_1517_;
v_isShared_1528_ = v_isSharedCheck_1541_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snapshotTasks_1525_);
lean_inc(v_infoState_1524_);
lean_inc(v_messages_1523_);
lean_inc(v_traceState_1522_);
lean_inc(v_auxDeclNGen_1521_);
lean_inc(v_ngen_1520_);
lean_inc(v_nextMacroScope_1519_);
lean_inc(v_env_1518_);
lean_dec(v___x_1517_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1541_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v_asyncMode_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1529_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1530_ = lean_ctor_get(v___x_1529_, 2);
v___f_1531_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1531_, 0, v_eqThms_1514_);
lean_closure_set(v___f_1531_, 1, v_declName_1513_);
v___x_1532_ = lean_box(0);
v___x_1533_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1529_, v_env_1518_, v___f_1531_, v_asyncMode_1530_, v___x_1532_);
v___x_1534_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 5, v___x_1534_);
lean_ctor_set(v___x_1527_, 0, v___x_1533_);
v___x_1536_ = v___x_1527_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_nextMacroScope_1519_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_ngen_1520_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_auxDeclNGen_1521_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_traceState_1522_);
lean_ctor_set(v_reuseFailAlloc_1540_, 5, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1540_, 6, v_messages_1523_);
lean_ctor_set(v_reuseFailAlloc_1540_, 7, v_infoState_1524_);
lean_ctor_set(v_reuseFailAlloc_1540_, 8, v_snapshotTasks_1525_);
v___x_1536_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_st_ref_set(v_a_1515_, v___x_1536_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1543_, lean_object* v_eqThms_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1543_, v_eqThms_1544_, v_a_1545_);
lean_dec(v_a_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1548_, lean_object* v_eqThms_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1548_, v_eqThms_1549_, v_a_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1554_, lean_object* v_eqThms_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1554_, v_eqThms_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_, lean_object* v_x_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1561_, v_x_1562_, v_x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1565_, lean_object* v_x_1566_, size_t v_x_1567_, size_t v_x_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1566_, v_x_1567_, v_x_1568_, v_x_1569_, v_x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_){
_start:
{
size_t v_x_887__boxed_1578_; size_t v_x_888__boxed_1579_; lean_object* v_res_1580_; 
v_x_887__boxed_1578_ = lean_unbox_usize(v_x_1574_);
lean_dec(v_x_1574_);
v_x_888__boxed_1579_ = lean_unbox_usize(v_x_1575_);
lean_dec(v_x_1575_);
v_res_1580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1572_, v_x_1573_, v_x_887__boxed_1578_, v_x_888__boxed_1579_, v_x_1576_, v_x_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1581_, lean_object* v_n_1582_, lean_object* v_k_1583_, lean_object* v_v_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1582_, v_k_1583_, v_v_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1586_, size_t v_depth_1587_, lean_object* v_keys_1588_, lean_object* v_vals_1589_, lean_object* v_heq_1590_, lean_object* v_i_1591_, lean_object* v_entries_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1587_, v_keys_1588_, v_vals_1589_, v_i_1591_, v_entries_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1594_, lean_object* v_depth_1595_, lean_object* v_keys_1596_, lean_object* v_vals_1597_, lean_object* v_heq_1598_, lean_object* v_i_1599_, lean_object* v_entries_1600_){
_start:
{
size_t v_depth_boxed_1601_; lean_object* v_res_1602_; 
v_depth_boxed_1601_ = lean_unbox_usize(v_depth_1595_);
lean_dec(v_depth_1595_);
v_res_1602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1594_, v_depth_boxed_1601_, v_keys_1596_, v_vals_1597_, v_heq_1598_, v_i_1599_, v_entries_1600_);
lean_dec_ref(v_vals_1597_);
lean_dec_ref(v_keys_1596_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1604_, v_x_1605_, v_x_1606_, v_x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1609_, lean_object* v_env_1610_, lean_object* v_idx_1611_, lean_object* v_eqs_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_nextEq_1619_; uint8_t v___x_1620_; 
v___x_1614_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_add(v_idx_1611_, v___x_1615_);
lean_dec(v_idx_1611_);
lean_inc(v___x_1616_);
v___x_1617_ = l_Nat_reprFast(v___x_1616_);
v___x_1618_ = lean_string_append(v___x_1614_, v___x_1617_);
lean_dec_ref(v___x_1617_);
lean_inc(v_declName_1609_);
lean_inc_ref(v_env_1610_);
v_nextEq_1619_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1610_, v_declName_1609_, v___x_1618_);
v___x_1620_ = l_Lean_Environment_containsOnBranch(v_env_1610_, v_nextEq_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v_nextEq_1619_);
lean_dec(v___x_1616_);
lean_dec_ref(v_env_1610_);
lean_dec(v_declName_1609_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_eqs_1612_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_array_push(v_eqs_1612_, v_nextEq_1619_);
v_idx_1611_ = v___x_1616_;
v_eqs_1612_ = v___x_1622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1624_, lean_object* v_env_1625_, lean_object* v_idx_1626_, lean_object* v_eqs_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1624_, v_env_1625_, v_idx_1626_, v_eqs_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1630_, lean_object* v_env_1631_, lean_object* v_idx_1632_, lean_object* v_eqs_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1630_, v_env_1631_, v_idx_1632_, v_eqs_1633_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1640_, lean_object* v_env_1641_, lean_object* v_idx_1642_, lean_object* v_eqs_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1640_, v_env_1641_, v_idx_1642_, v_eqs_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v_env_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; uint8_t v___x_1658_; 
v___x_1653_ = lean_st_ref_get(v_a_1651_);
v_env_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc_ref_n(v_env_1654_, 3);
lean_dec(v___x_1653_);
v___x_1655_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1650_);
v___x_1656_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1654_, v_declName_1650_, v___x_1655_);
v___x_1657_ = 1;
lean_inc(v___x_1656_);
v___x_1658_ = l_Lean_Environment_contains(v_env_1654_, v___x_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v___x_1656_);
lean_dec_ref(v_env_1654_);
lean_dec(v_declName_1650_);
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_mk_empty_array_with_capacity(v___x_1661_);
v___x_1663_ = lean_array_push(v___x_1662_, v___x_1656_);
lean_inc(v_declName_1650_);
v___x_1664_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1650_, v_env_1654_, v___x_1661_, v___x_1663_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1674_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc_n(v_a_1665_, 2);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1650_, v_a_1665_, v_a_1651_);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v___x_1666_, 0);
lean_dec(v_unused_1675_);
v___x_1668_ = v___x_1666_;
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
else
{
lean_dec(v___x_1666_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_a_1665_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1670_);
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_declName_1650_);
v_a_1676_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1664_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1664_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1684_, v_a_1685_);
lean_dec(v_a_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1688_, v_a_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1702_, lean_object* v_localInsts_1703_, lean_object* v_x_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1702_, v_localInsts_1703_, v_x_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v_a_1719_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1710_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1710_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1727_, lean_object* v_localInsts_1728_, lean_object* v_x_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1727_, v_localInsts_1728_, v_x_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1736_, lean_object* v_lctx_1737_, lean_object* v_localInsts_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1737_, v_localInsts_1738_, v_x_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_lctx_1747_, lean_object* v_localInsts_1748_, lean_object* v_x_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1746_, v_lctx_1747_, v_localInsts_1748_, v_x_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1759_, lean_object* v_as_x27_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
if (lean_obj_tag(v_as_x27_1760_) == 0)
{
lean_object* v___x_1767_; 
lean_dec(v_declName_1759_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_b_1761_);
return v___x_1767_;
}
else
{
lean_object* v_head_1768_; lean_object* v_tail_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v_b_1761_);
v_head_1768_ = lean_ctor_get(v_as_x27_1760_, 0);
v_tail_1769_ = lean_ctor_get(v_as_x27_1760_, 1);
lean_inc(v_head_1768_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
lean_inc(v_declName_1759_);
v___x_1770_ = lean_apply_6(v_head_1768_, v_declName_1759_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, lean_box(0));
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = lean_box(0);
if (lean_obj_tag(v_a_1771_) == 1)
{
lean_object* v_val_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1783_; 
v_val_1773_ = lean_ctor_get(v_a_1771_, 0);
lean_inc(v_val_1773_);
v___x_1774_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1759_, v_val_1773_, v___y_1765_);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v___x_1774_, 0);
lean_dec(v_unused_1784_);
v___x_1776_ = v___x_1774_;
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v___x_1774_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_a_1771_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v___x_1772_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v___x_1785_; 
lean_dec(v_a_1771_);
v___x_1785_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1760_ = v_tail_1769_;
v_b_1761_ = v___x_1785_;
goto _start;
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_declName_1759_);
v_a_1787_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1770_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1770_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1795_, lean_object* v_as_x27_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1795_, v_as_x27_1796_, v_b_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v_as_x27_1796_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
lean_inc(v_declName_1804_);
v___x_1810_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1848_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1848_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1848_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_unbox(v_a_1811_);
lean_dec(v_a_1811_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec(v_declName_1804_);
v___x_1816_ = lean_box(0);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1816_);
v___x_1818_ = v___x_1813_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
else
{
lean_object* v___x_1820_; 
lean_del_object(v___x_1813_);
lean_inc(v_declName_1804_);
v___x_1820_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1804_, v___y_1808_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
if (lean_obj_tag(v_a_1821_) == 1)
{
lean_dec_ref_known(v_a_1821_, 1);
lean_dec(v_declName_1804_);
return v___x_1820_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v___x_1822_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1823_ = lean_st_ref_get(v___x_1822_);
v___x_1824_ = lean_box(0);
v___x_1825_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1826_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1804_, v___x_1823_, v___x_1825_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___x_1823_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1839_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1839_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1839_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_fst_1831_; 
v_fst_1831_ = lean_ctor_get(v_a_1827_, 0);
lean_inc(v_fst_1831_);
lean_dec(v_a_1827_);
if (lean_obj_tag(v_fst_1831_) == 0)
{
lean_object* v___x_1833_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1824_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1824_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
else
{
lean_object* v_val_1835_; lean_object* v___x_1837_; 
v_val_1835_ = lean_ctor_get(v_fst_1831_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v_fst_1831_, 1);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v_val_1835_);
v___x_1837_ = v___x_1829_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_val_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1826_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1826_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
else
{
lean_dec(v_declName_1804_);
return v___x_1820_;
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_declName_1804_);
v_a_1849_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1810_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1810_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1864_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
return v___x_1866_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = lean_box(1);
v___x_1868_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1869_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v___x_1868_);
lean_ctor_set(v___x_1870_, 2, v___x_1867_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___f_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___f_1879_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1879_, 0, v_declName_1873_);
v___x_1880_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1881_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1882_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1880_, v___x_1881_, v___f_1879_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1890_, lean_object* v_as_1891_, lean_object* v_as_x27_1892_, lean_object* v_b_1893_, lean_object* v_a_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1890_, v_as_x27_1892_, v_b_1893_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1901_, lean_object* v_as_1902_, lean_object* v_as_x27_1903_, lean_object* v_b_1904_, lean_object* v_a_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1901_, v_as_1902_, v_as_x27_1903_, v_b_1904_, v_a_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v_as_x27_1903_);
lean_dec(v_as_1902_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1918_ = lean_unsigned_to_nat(32u);
v___x_1919_ = lean_mk_empty_array_with_capacity(v___x_1918_);
lean_dec_ref(v___x_1919_);
v___x_1920_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1921_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1912_);
v___x_1922_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1922_, 0, v_declName_1912_);
v___x_1923_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1923_, 0, lean_box(0));
lean_closure_set(v___x_1923_, 1, v_declName_1912_);
lean_closure_set(v___x_1923_, 2, v___x_1922_);
v___x_1924_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1920_, v___x_1921_, v___x_1923_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v_env_1939_; lean_object* v___x_1940_; lean_object* v_mctx_1941_; lean_object* v_lctx_1942_; lean_object* v_options_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1938_ = lean_st_ref_get(v___y_1936_);
v_env_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc_ref(v_env_1939_);
lean_dec(v___x_1938_);
v___x_1940_ = lean_st_ref_get(v___y_1934_);
v_mctx_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_mctx_1941_);
lean_dec(v___x_1940_);
v_lctx_1942_ = lean_ctor_get(v___y_1933_, 2);
v_options_1943_ = lean_ctor_get(v___y_1935_, 2);
lean_inc_ref(v_options_1943_);
lean_inc_ref(v_lctx_1942_);
v___x_1944_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1944_, 0, v_env_1939_);
lean_ctor_set(v___x_1944_, 1, v_mctx_1941_);
lean_ctor_set(v___x_1944_, 2, v_lctx_1942_);
lean_ctor_set(v___x_1944_, 3, v_options_1943_);
v___x_1945_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v_msgData_1932_);
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1953_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1954_; double v___x_1955_; 
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_float_of_nat(v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1959_, lean_object* v_msg_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_ref_1966_; lean_object* v___x_1967_; lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2012_; 
v_ref_1966_ = lean_ctor_get(v___y_1963_, 5);
v___x_1967_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_2012_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2012_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v_traceState_1973_; lean_object* v_env_1974_; lean_object* v_nextMacroScope_1975_; lean_object* v_ngen_1976_; lean_object* v_auxDeclNGen_1977_; lean_object* v_cache_1978_; lean_object* v_messages_1979_; lean_object* v_infoState_1980_; lean_object* v_snapshotTasks_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2011_; 
v___x_1972_ = lean_st_ref_take(v___y_1964_);
v_traceState_1973_ = lean_ctor_get(v___x_1972_, 4);
v_env_1974_ = lean_ctor_get(v___x_1972_, 0);
v_nextMacroScope_1975_ = lean_ctor_get(v___x_1972_, 1);
v_ngen_1976_ = lean_ctor_get(v___x_1972_, 2);
v_auxDeclNGen_1977_ = lean_ctor_get(v___x_1972_, 3);
v_cache_1978_ = lean_ctor_get(v___x_1972_, 5);
v_messages_1979_ = lean_ctor_get(v___x_1972_, 6);
v_infoState_1980_ = lean_ctor_get(v___x_1972_, 7);
v_snapshotTasks_1981_ = lean_ctor_get(v___x_1972_, 8);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1983_ = v___x_1972_;
v_isShared_1984_ = v_isSharedCheck_2011_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_snapshotTasks_1981_);
lean_inc(v_infoState_1980_);
lean_inc(v_messages_1979_);
lean_inc(v_cache_1978_);
lean_inc(v_traceState_1973_);
lean_inc(v_auxDeclNGen_1977_);
lean_inc(v_ngen_1976_);
lean_inc(v_nextMacroScope_1975_);
lean_inc(v_env_1974_);
lean_dec(v___x_1972_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2011_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
uint64_t v_tid_1985_; lean_object* v_traces_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2010_; 
v_tid_1985_ = lean_ctor_get_uint64(v_traceState_1973_, sizeof(void*)*1);
v_traces_1986_ = lean_ctor_get(v_traceState_1973_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_traceState_1973_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1988_ = v_traceState_1973_;
v_isShared_1989_ = v_isSharedCheck_2010_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_traces_1986_);
lean_dec(v_traceState_1973_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2010_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; double v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1990_ = lean_box(0);
v___x_1991_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_1992_ = 0;
v___x_1993_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_1994_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1994_, 0, v_cls_1959_);
lean_ctor_set(v___x_1994_, 1, v___x_1990_);
lean_ctor_set(v___x_1994_, 2, v___x_1993_);
lean_ctor_set_float(v___x_1994_, sizeof(void*)*3, v___x_1991_);
lean_ctor_set_float(v___x_1994_, sizeof(void*)*3 + 8, v___x_1991_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*3 + 16, v___x_1992_);
v___x_1995_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_1996_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v_a_1968_);
lean_ctor_set(v___x_1996_, 2, v___x_1995_);
lean_inc(v_ref_1966_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v_ref_1966_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Lean_PersistentArray_push___redArg(v_traces_1986_, v___x_1997_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1998_);
v___x_2000_ = v___x_1988_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_1998_);
lean_ctor_set_uint64(v_reuseFailAlloc_2009_, sizeof(void*)*1, v_tid_1985_);
v___x_2000_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v___x_2000_);
v___x_2002_ = v___x_1983_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_env_1974_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_nextMacroScope_1975_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_ngen_1976_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_auxDeclNGen_1977_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2008_, 5, v_cache_1978_);
lean_ctor_set(v_reuseFailAlloc_2008_, 6, v_messages_1979_);
lean_ctor_set(v_reuseFailAlloc_2008_, 7, v_infoState_1980_);
lean_ctor_set(v_reuseFailAlloc_2008_, 8, v_snapshotTasks_1981_);
v___x_2002_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2003_ = lean_st_ref_set(v___y_1964_, v___x_2002_);
v___x_2004_ = lean_box(0);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_2004_);
v___x_2006_ = v___x_1970_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2013_, lean_object* v_msg_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2013_, v_msg_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2021_, lean_object* v_as_2022_, size_t v_sz_2023_, size_t v_i_2024_, lean_object* v_b_2025_){
_start:
{
lean_object* v_a_2028_; uint8_t v___x_2032_; 
v___x_2032_ = lean_usize_dec_lt(v_i_2024_, v_sz_2023_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_b_2025_);
return v___x_2033_;
}
else
{
lean_object* v_a_2034_; lean_object* v_defValue_2035_; uint8_t v___x_2036_; uint8_t v___y_2038_; 
v_a_2034_ = lean_array_uget(v_as_2022_, v_i_2024_);
v_defValue_2035_ = lean_ctor_get(v_a_2034_, 1);
v___x_2036_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2021_, v_a_2034_);
if (v___x_2036_ == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = lean_unbox(v_defValue_2035_);
if (v___x_2050_ == 0)
{
v___y_2038_ = v___x_2032_;
goto v___jp_2037_;
}
else
{
v___y_2038_ = v___x_2036_;
goto v___jp_2037_;
}
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_unbox(v_defValue_2035_);
v___y_2038_ = v___x_2051_;
goto v___jp_2037_;
}
v___jp_2037_:
{
if (v___y_2038_ == 0)
{
lean_object* v_name_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2048_; 
v_name_2039_ = lean_ctor_get(v_a_2034_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_a_2034_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; 
v_unused_2049_ = lean_ctor_get(v_a_2034_, 1);
lean_dec(v_unused_2049_);
v___x_2041_ = v_a_2034_;
v_isShared_2042_ = v_isSharedCheck_2048_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_name_2039_);
lean_dec(v_a_2034_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2048_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2043_, 0, v___x_2036_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 1, v___x_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_name_2039_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_array_push(v_b_2025_, v___x_2045_);
v_a_2028_ = v___x_2046_;
goto v___jp_2027_;
}
}
}
else
{
lean_dec(v_a_2034_);
v_a_2028_ = v_b_2025_;
goto v___jp_2027_;
}
}
}
v___jp_2027_:
{
size_t v___x_2029_; size_t v___x_2030_; 
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_add(v_i_2024_, v___x_2029_);
v_i_2024_ = v___x_2030_;
v_b_2025_ = v_a_2028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2052_, lean_object* v_as_2053_, lean_object* v_sz_2054_, lean_object* v_i_2055_, lean_object* v_b_2056_, lean_object* v___y_2057_){
_start:
{
size_t v_sz_boxed_2058_; size_t v_i_boxed_2059_; lean_object* v_res_2060_; 
v_sz_boxed_2058_ = lean_unbox_usize(v_sz_2054_);
lean_dec(v_sz_2054_);
v_i_boxed_2059_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2052_, v_as_2053_, v_sz_boxed_2058_, v_i_boxed_2059_, v_b_2056_);
lean_dec_ref(v_as_2053_);
lean_dec_ref(v___x_2052_);
return v_res_2060_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2063_; size_t v_sz_2064_; 
v___x_2063_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2064_ = lean_array_size(v___x_2063_);
return v_sz_2064_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2066_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
lean_ctor_set(v___x_2066_, 2, v___x_2065_);
lean_ctor_set(v___x_2066_, 3, v___x_2065_);
lean_ctor_set(v___x_2066_, 4, v___x_2065_);
lean_ctor_set(v___x_2066_, 5, v___x_2065_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2075_ = l_Lean_Name_append(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2078_ = l_Lean_stringToMessageData(v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_options_2085_; lean_object* v_inheritedTraceOptions_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; size_t v_sz_2090_; size_t v___x_2091_; lean_object* v___x_2092_; 
v_options_2085_ = lean_ctor_get(v_a_2082_, 2);
v_inheritedTraceOptions_2086_ = lean_ctor_get(v_a_2082_, 13);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2089_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2090_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2091_ = ((size_t)0ULL);
v___x_2092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2085_, v___x_2089_, v_sz_2090_, v___x_2091_, v___x_2088_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2152_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2152_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2152_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = lean_array_get_size(v_a_2093_);
v___x_2141_ = lean_nat_dec_eq(v___x_2140_, v___x_2087_);
if (v___x_2141_ == 0)
{
uint8_t v_hasTrace_2142_; 
v_hasTrace_2142_ = lean_ctor_get_uint8(v_options_2085_, sizeof(void*)*1);
if (v_hasTrace_2142_ == 0)
{
v___y_2098_ = v_a_2081_;
v___y_2099_ = v_a_2083_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2143_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2144_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2145_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2086_, v_options_2085_, v___x_2144_);
if (v___x_2145_ == 0)
{
v___y_2098_ = v_a_2081_;
v___y_2099_ = v_a_2083_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2146_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2079_);
v___x_2147_ = l_Lean_MessageData_ofName(v_declName_2079_);
v___x_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2143_, v___x_2148_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_dec_ref_known(v___x_2149_, 1);
v___y_2098_ = v_a_2081_;
v___y_2099_ = v_a_2083_;
goto v___jp_2097_;
}
else
{
lean_del_object(v___x_2095_);
lean_dec(v_a_2093_);
lean_dec(v_declName_2079_);
return v___x_2149_;
}
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_del_object(v___x_2095_);
lean_dec(v_a_2093_);
lean_dec(v_declName_2079_);
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
v___jp_2097_:
{
lean_object* v___x_2100_; lean_object* v_env_2101_; lean_object* v_nextMacroScope_2102_; lean_object* v_ngen_2103_; lean_object* v_auxDeclNGen_2104_; lean_object* v_traceState_2105_; lean_object* v_messages_2106_; lean_object* v_infoState_2107_; lean_object* v_snapshotTasks_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2138_; 
v___x_2100_ = lean_st_ref_take(v___y_2099_);
v_env_2101_ = lean_ctor_get(v___x_2100_, 0);
v_nextMacroScope_2102_ = lean_ctor_get(v___x_2100_, 1);
v_ngen_2103_ = lean_ctor_get(v___x_2100_, 2);
v_auxDeclNGen_2104_ = lean_ctor_get(v___x_2100_, 3);
v_traceState_2105_ = lean_ctor_get(v___x_2100_, 4);
v_messages_2106_ = lean_ctor_get(v___x_2100_, 6);
v_infoState_2107_ = lean_ctor_get(v___x_2100_, 7);
v_snapshotTasks_2108_ = lean_ctor_get(v___x_2100_, 8);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; 
v_unused_2139_ = lean_ctor_get(v___x_2100_, 5);
lean_dec(v_unused_2139_);
v___x_2110_ = v___x_2100_;
v_isShared_2111_ = v_isSharedCheck_2138_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_snapshotTasks_2108_);
lean_inc(v_infoState_2107_);
lean_inc(v_messages_2106_);
lean_inc(v_traceState_2105_);
lean_inc(v_auxDeclNGen_2104_);
lean_inc(v_ngen_2103_);
lean_inc(v_nextMacroScope_2102_);
lean_inc(v_env_2101_);
lean_dec(v___x_2100_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2138_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2112_ = l_Lean_Meta_eqnOptionsExt;
v___x_2113_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2112_, v_env_2101_, v_declName_2079_, v_a_2093_);
v___x_2114_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 5, v___x_2114_);
lean_ctor_set(v___x_2110_, 0, v___x_2113_);
v___x_2116_ = v___x_2110_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_nextMacroScope_2102_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_ngen_2103_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v_auxDeclNGen_2104_);
lean_ctor_set(v_reuseFailAlloc_2137_, 4, v_traceState_2105_);
lean_ctor_set(v_reuseFailAlloc_2137_, 5, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2137_, 6, v_messages_2106_);
lean_ctor_set(v_reuseFailAlloc_2137_, 7, v_infoState_2107_);
lean_ctor_set(v_reuseFailAlloc_2137_, 8, v_snapshotTasks_2108_);
v___x_2116_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_mctx_2119_; lean_object* v_zetaDeltaFVarIds_2120_; lean_object* v_postponed_2121_; lean_object* v_diag_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2135_; 
v___x_2117_ = lean_st_ref_set(v___y_2099_, v___x_2116_);
v___x_2118_ = lean_st_ref_take(v___y_2098_);
v_mctx_2119_ = lean_ctor_get(v___x_2118_, 0);
v_zetaDeltaFVarIds_2120_ = lean_ctor_get(v___x_2118_, 2);
v_postponed_2121_ = lean_ctor_get(v___x_2118_, 3);
v_diag_2122_ = lean_ctor_get(v___x_2118_, 4);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v___x_2118_, 1);
lean_dec(v_unused_2136_);
v___x_2124_ = v___x_2118_;
v_isShared_2125_ = v_isSharedCheck_2135_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_diag_2122_);
lean_inc(v_postponed_2121_);
lean_inc(v_zetaDeltaFVarIds_2120_);
lean_inc(v_mctx_2119_);
lean_dec(v___x_2118_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2135_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_mctx_2119_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_zetaDeltaFVarIds_2120_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_postponed_2121_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_diag_2122_);
v___x_2128_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2129_ = lean_st_ref_set(v___y_2098_, v___x_2128_);
v___x_2130_ = lean_box(0);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2130_);
v___x_2132_ = v___x_2095_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
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
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_declName_2079_);
v_a_2153_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2092_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2092_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2168_, lean_object* v_as_2169_, size_t v_sz_2170_, size_t v_i_2171_, lean_object* v_b_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2168_, v_as_2169_, v_sz_2170_, v_i_2171_, v_b_2172_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2179_, lean_object* v_as_2180_, lean_object* v_sz_2181_, lean_object* v_i_2182_, lean_object* v_b_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
size_t v_sz_boxed_2189_; size_t v_i_boxed_2190_; lean_object* v_res_2191_; 
v_sz_boxed_2189_ = lean_unbox_usize(v_sz_2181_);
lean_dec(v_sz_2181_);
v_i_boxed_2190_ = lean_unbox_usize(v_i_2182_);
lean_dec(v_i_2182_);
v_res_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2179_, v_as_2180_, v_sz_boxed_2189_, v_i_boxed_2190_, v_b_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_as_2180_);
lean_dec_ref(v___x_2179_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_st_mk_ref(v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2198_){
_start:
{
uint8_t v___x_2200_; 
v___x_2200_ = l_Lean_initializing();
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v_f_2198_);
v___x_2201_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2203_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2204_ = lean_st_ref_take(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_f_2198_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_st_ref_set(v___x_2203_, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2214_, lean_object* v_as_x27_2215_, lean_object* v_b_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
if (lean_obj_tag(v_as_x27_2215_) == 0)
{
lean_object* v___x_2222_; 
lean_dec(v_declName_2214_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_b_2216_);
return v___x_2222_;
}
else
{
lean_object* v_head_2223_; lean_object* v_tail_2224_; lean_object* v___x_2225_; 
lean_dec_ref(v_b_2216_);
v_head_2223_ = lean_ctor_get(v_as_x27_2215_, 0);
v_tail_2224_ = lean_ctor_get(v_as_x27_2215_, 1);
lean_inc(v_head_2223_);
lean_inc(v___y_2220_);
lean_inc_ref(v___y_2219_);
lean_inc(v___y_2218_);
lean_inc_ref(v___y_2217_);
lean_inc(v_declName_2214_);
v___x_2225_ = lean_apply_6(v_head_2223_, v_declName_2214_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, lean_box(0));
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2238_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_box(0);
if (lean_obj_tag(v_a_2226_) == 1)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_dec(v_declName_2214_);
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_a_2226_);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2232_);
v___x_2234_ = v___x_2228_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v___x_2236_; 
lean_del_object(v___x_2228_);
lean_dec(v_a_2226_);
v___x_2236_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2215_ = v_tail_2224_;
v_b_2216_ = v___x_2236_;
goto _start;
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_declName_2214_);
v_a_2239_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2225_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2225_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2247_, lean_object* v_as_x27_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2247_, v_as_x27_2248_, v_b_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v_as_x27_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2256_, lean_object* v_declName_2257_, uint8_t v_nonRec_2258_, lean_object* v___x_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2268_; lean_object* v_env_2269_; uint8_t v___x_2270_; uint8_t v___x_2271_; 
v___x_2268_ = lean_st_ref_get(v___y_2263_);
v_env_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc_ref(v_env_2269_);
lean_dec(v___x_2268_);
v___x_2270_ = 1;
lean_inc(v___x_2256_);
v___x_2271_ = l_Lean_Environment_contains(v_env_2269_, v___x_2256_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
lean_dec(v___x_2256_);
lean_inc(v_declName_2257_);
v___x_2272_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2257_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; uint8_t v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v___x_2274_ = lean_unbox(v_a_2273_);
lean_dec(v_a_2273_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v___x_2259_);
lean_dec(v_declName_2257_);
goto v___jp_2265_;
}
else
{
lean_object* v___x_2275_; 
lean_inc(v_declName_2257_);
v___x_2275_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2257_, v___y_2263_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; uint8_t v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v___x_2277_ = lean_unbox(v_a_2276_);
lean_dec(v_a_2276_);
if (v___x_2277_ == 0)
{
if (v_nonRec_2258_ == 0)
{
lean_dec_ref(v___x_2259_);
lean_dec(v_declName_2257_);
goto v___jp_2265_;
}
else
{
lean_object* v___x_2278_; lean_object* v_env_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2278_ = lean_st_ref_get(v___y_2263_);
v_env_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_ref(v_env_2279_);
lean_dec(v___x_2278_);
lean_inc(v_declName_2257_);
v___x_2280_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2279_, v_declName_2257_, v___x_2259_);
v___x_2281_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2257_, v___x_2280_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2281_;
}
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v___x_2259_);
v___x_2282_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2283_ = lean_st_ref_get(v___x_2282_);
v___x_2284_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2285_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2257_, v___x_2283_, v___x_2284_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___x_2283_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2295_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_fst_2290_; 
v_fst_2290_ = lean_ctor_get(v_a_2286_, 0);
lean_inc(v_fst_2290_);
lean_dec(v_a_2286_);
if (lean_obj_tag(v_fst_2290_) == 0)
{
lean_del_object(v___x_2288_);
goto v___jp_2265_;
}
else
{
lean_object* v_val_2291_; lean_object* v___x_2293_; 
v_val_2291_ = lean_ctor_get(v_fst_2290_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v_fst_2290_, 1);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v_val_2291_);
v___x_2293_ = v___x_2288_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_val_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
v_a_2296_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2285_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2285_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v___x_2259_);
lean_dec(v_declName_2257_);
v_a_2304_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2275_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2275_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v___x_2259_);
lean_dec(v_declName_2257_);
v_a_2312_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2272_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2272_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec_ref(v___x_2259_);
lean_dec(v_declName_2257_);
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2256_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
v___jp_2265_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2322_, lean_object* v_declName_2323_, lean_object* v_nonRec_2324_, lean_object* v___x_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v_nonRec_boxed_2331_; lean_object* v_res_2332_; 
v_nonRec_boxed_2331_ = lean_unbox(v_nonRec_2324_);
v_res_2332_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2322_, v_declName_2323_, v_nonRec_boxed_2331_, v___x_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_ref_2339_; lean_object* v___x_2340_; lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2349_; 
v_ref_2339_ = lean_ctor_get(v___y_2336_, 5);
v___x_2340_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_inc(v_ref_2339_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v_ref_2339_);
lean_ctor_set(v___x_2345_, 1, v_a_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 1);
lean_ctor_set(v___x_2343_, 0, v___x_2345_);
v___x_2347_ = v___x_2343_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2357_, uint8_t v_isExporting_2358_, lean_object* v___x_2359_, lean_object* v___y_2360_, lean_object* v___x_2361_, lean_object* v_a_x3f_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v_env_2365_; lean_object* v_nextMacroScope_2366_; lean_object* v_ngen_2367_; lean_object* v_auxDeclNGen_2368_; lean_object* v_traceState_2369_; lean_object* v_messages_2370_; lean_object* v_infoState_2371_; lean_object* v_snapshotTasks_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2397_; 
v___x_2364_ = lean_st_ref_take(v___y_2357_);
v_env_2365_ = lean_ctor_get(v___x_2364_, 0);
v_nextMacroScope_2366_ = lean_ctor_get(v___x_2364_, 1);
v_ngen_2367_ = lean_ctor_get(v___x_2364_, 2);
v_auxDeclNGen_2368_ = lean_ctor_get(v___x_2364_, 3);
v_traceState_2369_ = lean_ctor_get(v___x_2364_, 4);
v_messages_2370_ = lean_ctor_get(v___x_2364_, 6);
v_infoState_2371_ = lean_ctor_get(v___x_2364_, 7);
v_snapshotTasks_2372_ = lean_ctor_get(v___x_2364_, 8);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v___x_2364_, 5);
lean_dec(v_unused_2398_);
v___x_2374_ = v___x_2364_;
v_isShared_2375_ = v_isSharedCheck_2397_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_snapshotTasks_2372_);
lean_inc(v_infoState_2371_);
lean_inc(v_messages_2370_);
lean_inc(v_traceState_2369_);
lean_inc(v_auxDeclNGen_2368_);
lean_inc(v_ngen_2367_);
lean_inc(v_nextMacroScope_2366_);
lean_inc(v_env_2365_);
lean_dec(v___x_2364_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2397_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2376_ = l_Lean_Environment_setExporting(v_env_2365_, v_isExporting_2358_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 5, v___x_2359_);
lean_ctor_set(v___x_2374_, 0, v___x_2376_);
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_nextMacroScope_2366_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_ngen_2367_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_auxDeclNGen_2368_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v_traceState_2369_);
lean_ctor_set(v_reuseFailAlloc_2396_, 5, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2396_, 6, v_messages_2370_);
lean_ctor_set(v_reuseFailAlloc_2396_, 7, v_infoState_2371_);
lean_ctor_set(v_reuseFailAlloc_2396_, 8, v_snapshotTasks_2372_);
v___x_2378_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v_mctx_2381_; lean_object* v_zetaDeltaFVarIds_2382_; lean_object* v_postponed_2383_; lean_object* v_diag_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2394_; 
v___x_2379_ = lean_st_ref_set(v___y_2357_, v___x_2378_);
v___x_2380_ = lean_st_ref_take(v___y_2360_);
v_mctx_2381_ = lean_ctor_get(v___x_2380_, 0);
v_zetaDeltaFVarIds_2382_ = lean_ctor_get(v___x_2380_, 2);
v_postponed_2383_ = lean_ctor_get(v___x_2380_, 3);
v_diag_2384_ = lean_ctor_get(v___x_2380_, 4);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v___x_2380_, 1);
lean_dec(v_unused_2395_);
v___x_2386_ = v___x_2380_;
v_isShared_2387_ = v_isSharedCheck_2394_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_diag_2384_);
lean_inc(v_postponed_2383_);
lean_inc(v_zetaDeltaFVarIds_2382_);
lean_inc(v_mctx_2381_);
lean_dec(v___x_2380_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2394_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 1, v___x_2361_);
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_mctx_2381_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_zetaDeltaFVarIds_2382_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_postponed_2383_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v_diag_2384_);
v___x_2389_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = lean_st_ref_set(v___y_2360_, v___x_2389_);
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2399_, lean_object* v_isExporting_2400_, lean_object* v___x_2401_, lean_object* v___y_2402_, lean_object* v___x_2403_, lean_object* v_a_x3f_2404_, lean_object* v___y_2405_){
_start:
{
uint8_t v_isExporting_boxed_2406_; lean_object* v_res_2407_; 
v_isExporting_boxed_2406_ = lean_unbox(v_isExporting_2400_);
v_res_2407_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2399_, v_isExporting_boxed_2406_, v___x_2401_, v___y_2402_, v___x_2403_, v_a_x3f_2404_);
lean_dec(v_a_x3f_2404_);
lean_dec(v___y_2402_);
lean_dec(v___y_2399_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2408_, uint8_t v_isExporting_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_env_2416_; uint8_t v_isExporting_2417_; lean_object* v___x_2483_; uint8_t v_isModule_2484_; 
v___x_2415_ = lean_st_ref_get(v___y_2413_);
v_env_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_ref(v_env_2416_);
lean_dec(v___x_2415_);
v_isExporting_2417_ = lean_ctor_get_uint8(v_env_2416_, sizeof(void*)*8);
v___x_2483_ = l_Lean_Environment_header(v_env_2416_);
lean_dec_ref(v_env_2416_);
v_isModule_2484_ = lean_ctor_get_uint8(v___x_2483_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2483_);
if (v_isModule_2484_ == 0)
{
lean_object* v___x_2485_; 
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
v___x_2485_ = lean_apply_5(v_x_2408_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2485_;
}
else
{
if (v_isExporting_2417_ == 0)
{
if (v_isExporting_2409_ == 0)
{
lean_object* v___x_2486_; 
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
v___x_2486_ = lean_apply_5(v_x_2408_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2486_;
}
else
{
goto v___jp_2418_;
}
}
else
{
if (v_isExporting_2409_ == 0)
{
goto v___jp_2418_;
}
else
{
lean_object* v___x_2487_; 
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
v___x_2487_ = lean_apply_5(v_x_2408_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2487_;
}
}
}
v___jp_2418_:
{
lean_object* v___x_2419_; lean_object* v_env_2420_; lean_object* v_nextMacroScope_2421_; lean_object* v_ngen_2422_; lean_object* v_auxDeclNGen_2423_; lean_object* v_traceState_2424_; lean_object* v_messages_2425_; lean_object* v_infoState_2426_; lean_object* v_snapshotTasks_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2481_; 
v___x_2419_ = lean_st_ref_take(v___y_2413_);
v_env_2420_ = lean_ctor_get(v___x_2419_, 0);
v_nextMacroScope_2421_ = lean_ctor_get(v___x_2419_, 1);
v_ngen_2422_ = lean_ctor_get(v___x_2419_, 2);
v_auxDeclNGen_2423_ = lean_ctor_get(v___x_2419_, 3);
v_traceState_2424_ = lean_ctor_get(v___x_2419_, 4);
v_messages_2425_ = lean_ctor_get(v___x_2419_, 6);
v_infoState_2426_ = lean_ctor_get(v___x_2419_, 7);
v_snapshotTasks_2427_ = lean_ctor_get(v___x_2419_, 8);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2419_, 5);
lean_dec(v_unused_2482_);
v___x_2429_ = v___x_2419_;
v_isShared_2430_ = v_isSharedCheck_2481_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_snapshotTasks_2427_);
lean_inc(v_infoState_2426_);
lean_inc(v_messages_2425_);
lean_inc(v_traceState_2424_);
lean_inc(v_auxDeclNGen_2423_);
lean_inc(v_ngen_2422_);
lean_inc(v_nextMacroScope_2421_);
lean_inc(v_env_2420_);
lean_dec(v___x_2419_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2481_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2431_ = l_Lean_Environment_setExporting(v_env_2420_, v_isExporting_2409_);
v___x_2432_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 5, v___x_2432_);
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2434_ = v___x_2429_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_nextMacroScope_2421_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_ngen_2422_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_auxDeclNGen_2423_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_traceState_2424_);
lean_ctor_set(v_reuseFailAlloc_2480_, 5, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2480_, 6, v_messages_2425_);
lean_ctor_set(v_reuseFailAlloc_2480_, 7, v_infoState_2426_);
lean_ctor_set(v_reuseFailAlloc_2480_, 8, v_snapshotTasks_2427_);
v___x_2434_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v_mctx_2437_; lean_object* v_zetaDeltaFVarIds_2438_; lean_object* v_postponed_2439_; lean_object* v_diag_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2478_; 
v___x_2435_ = lean_st_ref_set(v___y_2413_, v___x_2434_);
v___x_2436_ = lean_st_ref_take(v___y_2411_);
v_mctx_2437_ = lean_ctor_get(v___x_2436_, 0);
v_zetaDeltaFVarIds_2438_ = lean_ctor_get(v___x_2436_, 2);
v_postponed_2439_ = lean_ctor_get(v___x_2436_, 3);
v_diag_2440_ = lean_ctor_get(v___x_2436_, 4);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2436_, 1);
lean_dec(v_unused_2479_);
v___x_2442_ = v___x_2436_;
v_isShared_2443_ = v_isSharedCheck_2478_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_diag_2440_);
lean_inc(v_postponed_2439_);
lean_inc(v_zetaDeltaFVarIds_2438_);
lean_inc(v_mctx_2437_);
lean_dec(v___x_2436_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2478_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 1, v___x_2444_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_mctx_2437_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_zetaDeltaFVarIds_2438_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_postponed_2439_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_diag_2440_);
v___x_2446_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v_r_2448_; 
v___x_2447_ = lean_st_ref_set(v___y_2411_, v___x_2446_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
v_r_2448_ = lean_apply_5(v_x_2408_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
if (lean_obj_tag(v_r_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2465_; 
v_a_2449_ = lean_ctor_get(v_r_2448_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_r_2448_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2451_ = v_r_2448_;
v_isShared_2452_ = v_isSharedCheck_2465_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v_r_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2465_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
lean_inc(v_a_2449_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set_tag(v___x_2451_, 1);
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v___x_2455_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_2417_, v___x_2432_, v___y_2411_, v___x_2444_, v___x_2454_);
lean_dec_ref(v___x_2454_);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; 
v_unused_2463_ = lean_ctor_get(v___x_2455_, 0);
lean_dec(v_unused_2463_);
v___x_2457_ = v___x_2455_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_dec(v___x_2455_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v_a_2449_);
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2449_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2466_ = lean_ctor_get(v_r_2448_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v_r_2448_, 1);
v___x_2467_ = lean_box(0);
v___x_2468_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_2417_, v___x_2432_, v___y_2411_, v___x_2444_, v___x_2467_);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2468_, 0);
lean_dec(v_unused_2476_);
v___x_2470_ = v___x_2468_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_dec(v___x_2468_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set_tag(v___x_2470_, 1);
lean_ctor_set(v___x_2470_, 0, v_a_2466_);
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2466_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2488_, lean_object* v_isExporting_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v_isExporting_boxed_2495_; lean_object* v_res_2496_; 
v_isExporting_boxed_2495_ = lean_unbox(v_isExporting_2489_);
v_res_2496_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2488_, v_isExporting_boxed_2495_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2497_, uint8_t v_when_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
if (v_when_2498_ == 0)
{
lean_object* v___x_2504_; 
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
lean_inc(v___y_2500_);
lean_inc_ref(v___y_2499_);
v___x_2504_ = lean_apply_5(v_x_2497_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, lean_box(0));
return v___x_2504_;
}
else
{
uint8_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = 0;
v___x_2506_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2497_, v___x_2505_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2507_, lean_object* v_when_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
uint8_t v_when_boxed_2514_; lean_object* v_res_2515_; 
v_when_boxed_2514_ = lean_unbox(v_when_2508_);
v_res_2515_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2507_, v_when_boxed_2514_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2515_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2518_ = l_Lean_stringToMessageData(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2521_ = l_Lean_stringToMessageData(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2525_, uint8_t v_nonRec_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; lean_object* v_env_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2532_ = lean_st_ref_get(v___y_2530_);
v_env_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_ref(v_env_2533_);
lean_dec(v___x_2532_);
v___x_2534_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2525_);
v___x_2535_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2533_, v_declName_2525_, v___x_2534_);
v___x_2536_ = lean_box(v_nonRec_2526_);
lean_inc(v___x_2535_);
v___f_2537_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2537_, 0, v___x_2535_);
lean_closure_set(v___f_2537_, 1, v_declName_2525_);
lean_closure_set(v___f_2537_, 2, v___x_2536_);
lean_closure_set(v___f_2537_, 3, v___x_2534_);
v___x_2538_ = 1;
v___x_2539_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2537_, v___x_2538_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
if (lean_obj_tag(v_a_2540_) == 1)
{
lean_object* v_val_2541_; uint8_t v___x_2542_; 
v_val_2541_ = lean_ctor_get(v_a_2540_, 0);
lean_inc(v_val_2541_);
lean_dec_ref_known(v_a_2540_, 1);
v___x_2542_ = lean_name_eq(v_val_2541_, v___x_2535_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref_known(v___x_2539_, 1);
v___x_2543_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2544_ = l_Lean_MessageData_ofName(v_val_2541_);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = l_Lean_MessageData_ofName(v___x_2535_);
v___x_2549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2551_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
else
{
lean_dec(v_val_2541_);
lean_dec(v___x_2535_);
return v___x_2539_;
}
}
else
{
lean_dec(v_a_2540_);
lean_dec(v___x_2535_);
return v___x_2539_;
}
}
else
{
lean_dec(v___x_2535_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2561_, lean_object* v_nonRec_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
uint8_t v_nonRec_boxed_2568_; lean_object* v_res_2569_; 
v_nonRec_boxed_2568_ = lean_unbox(v_nonRec_2562_);
v_res_2569_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2561_, v_nonRec_boxed_2568_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2570_, uint8_t v_nonRec_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2577_ = lean_box(v_nonRec_2571_);
v___f_2578_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2578_, 0, v_declName_2570_);
lean_closure_set(v___f_2578_, 1, v___x_2577_);
v___x_2579_ = lean_unsigned_to_nat(32u);
v___x_2580_ = lean_mk_empty_array_with_capacity(v___x_2579_);
lean_dec_ref(v___x_2580_);
v___x_2581_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2583_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2581_, v___x_2582_, v___f_2578_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2584_, lean_object* v_nonRec_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
uint8_t v_nonRec_boxed_2591_; lean_object* v_res_2592_; 
v_nonRec_boxed_2591_ = lean_unbox(v_nonRec_2585_);
v_res_2592_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2584_, v_nonRec_boxed_2591_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2593_, lean_object* v_as_2594_, lean_object* v_as_x27_2595_, lean_object* v_b_2596_, lean_object* v_a_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2593_, v_as_x27_2595_, v_b_2596_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2604_, lean_object* v_as_2605_, lean_object* v_as_x27_2606_, lean_object* v_b_2607_, lean_object* v_a_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2604_, v_as_2605_, v_as_x27_2606_, v_b_2607_, v_a_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v_as_x27_2606_);
lean_dec(v_as_2605_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2615_, lean_object* v_x_2616_, uint8_t v_isExporting_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2616_, v_isExporting_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2624_, lean_object* v_x_2625_, lean_object* v_isExporting_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v_isExporting_boxed_2632_; lean_object* v_res_2633_; 
v_isExporting_boxed_2632_ = lean_unbox(v_isExporting_2626_);
v_res_2633_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2624_, v_x_2625_, v_isExporting_boxed_2632_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2634_, lean_object* v_x_2635_, uint8_t v_when_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2635_, v_when_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2643_, lean_object* v_x_2644_, lean_object* v_when_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
uint8_t v_when_boxed_2651_; lean_object* v_res_2652_; 
v_when_boxed_2651_ = lean_unbox(v_when_2645_);
v_res_2652_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2643_, v_x_2644_, v_when_boxed_2651_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2653_, lean_object* v_msg_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2661_, lean_object* v_msg_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2661_, v_msg_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
return v_res_2668_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = lean_unsigned_to_nat(32u);
v___x_2670_ = lean_mk_empty_array_with_capacity(v___x_2669_);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
return v___x_2671_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2672_ = ((size_t)5ULL);
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = lean_unsigned_to_nat(32u);
v___x_2675_ = lean_mk_empty_array_with_capacity(v___x_2674_);
v___x_2676_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2677_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___x_2675_);
lean_ctor_set(v___x_2677_, 2, v___x_2673_);
lean_ctor_set(v___x_2677_, 3, v___x_2673_);
lean_ctor_set_usize(v___x_2677_, 4, v___x_2672_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; lean_object* v_traceState_2681_; lean_object* v_traces_2682_; lean_object* v___x_2683_; lean_object* v_traceState_2684_; lean_object* v_env_2685_; lean_object* v_nextMacroScope_2686_; lean_object* v_ngen_2687_; lean_object* v_auxDeclNGen_2688_; lean_object* v_cache_2689_; lean_object* v_messages_2690_; lean_object* v_infoState_2691_; lean_object* v_snapshotTasks_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2711_; 
v___x_2680_ = lean_st_ref_get(v___y_2678_);
v_traceState_2681_ = lean_ctor_get(v___x_2680_, 4);
lean_inc_ref(v_traceState_2681_);
lean_dec(v___x_2680_);
v_traces_2682_ = lean_ctor_get(v_traceState_2681_, 0);
lean_inc_ref(v_traces_2682_);
lean_dec_ref(v_traceState_2681_);
v___x_2683_ = lean_st_ref_take(v___y_2678_);
v_traceState_2684_ = lean_ctor_get(v___x_2683_, 4);
v_env_2685_ = lean_ctor_get(v___x_2683_, 0);
v_nextMacroScope_2686_ = lean_ctor_get(v___x_2683_, 1);
v_ngen_2687_ = lean_ctor_get(v___x_2683_, 2);
v_auxDeclNGen_2688_ = lean_ctor_get(v___x_2683_, 3);
v_cache_2689_ = lean_ctor_get(v___x_2683_, 5);
v_messages_2690_ = lean_ctor_get(v___x_2683_, 6);
v_infoState_2691_ = lean_ctor_get(v___x_2683_, 7);
v_snapshotTasks_2692_ = lean_ctor_get(v___x_2683_, 8);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2694_ = v___x_2683_;
v_isShared_2695_ = v_isSharedCheck_2711_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_snapshotTasks_2692_);
lean_inc(v_infoState_2691_);
lean_inc(v_messages_2690_);
lean_inc(v_cache_2689_);
lean_inc(v_traceState_2684_);
lean_inc(v_auxDeclNGen_2688_);
lean_inc(v_ngen_2687_);
lean_inc(v_nextMacroScope_2686_);
lean_inc(v_env_2685_);
lean_dec(v___x_2683_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2711_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
uint64_t v_tid_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2709_; 
v_tid_2696_ = lean_ctor_get_uint64(v_traceState_2684_, sizeof(void*)*1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_traceState_2684_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; 
v_unused_2710_ = lean_ctor_get(v_traceState_2684_, 0);
lean_dec(v_unused_2710_);
v___x_2698_ = v_traceState_2684_;
v_isShared_2699_ = v_isSharedCheck_2709_;
goto v_resetjp_2697_;
}
else
{
lean_dec(v_traceState_2684_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2709_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2700_);
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2700_);
lean_ctor_set_uint64(v_reuseFailAlloc_2708_, sizeof(void*)*1, v_tid_2696_);
v___x_2702_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 4, v___x_2702_);
v___x_2704_ = v___x_2694_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_env_2685_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_nextMacroScope_2686_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_ngen_2687_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_auxDeclNGen_2688_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2707_, 5, v_cache_2689_);
lean_ctor_set(v_reuseFailAlloc_2707_, 6, v_messages_2690_);
lean_ctor_set(v_reuseFailAlloc_2707_, 7, v_infoState_2691_);
lean_ctor_set(v_reuseFailAlloc_2707_, 8, v_snapshotTasks_2692_);
v___x_2704_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_st_ref_set(v___y_2678_, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v_traces_2682_);
return v___x_2706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2712_);
lean_dec(v___y_2712_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = 0;
v___x_2728_ = lean_box(v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2737_ = l_Lean_stringToMessageData(v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2743_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2744_ = l_Lean_MessageData_ofName(v_name_2738_);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2747_, lean_object* v_x_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2747_, v_x_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v_x_2748_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2753_){
_start:
{
if (lean_obj_tag(v_x_2753_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v_x_2753_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_x_2753_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v_x_2753_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v_x_2753_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 1);
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
v_a_2763_ = lean_ctor_get(v_x_2753_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_x_2753_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v_x_2753_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v_x_2753_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 0);
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2774_){
_start:
{
if (lean_obj_tag(v_e_2774_) == 0)
{
uint8_t v___x_2775_; 
v___x_2775_ = 2;
return v___x_2775_;
}
else
{
lean_object* v_a_2776_; uint8_t v___x_2777_; 
v_a_2776_ = lean_ctor_get(v_e_2774_, 0);
v___x_2777_ = lean_unbox(v_a_2776_);
if (v___x_2777_ == 0)
{
uint8_t v___x_2778_; 
v___x_2778_ = 1;
return v___x_2778_;
}
else
{
uint8_t v___x_2779_; 
v___x_2779_ = 0;
return v___x_2779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2780_){
_start:
{
uint8_t v_res_2781_; lean_object* v_r_2782_; 
v_res_2781_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2780_);
lean_dec_ref(v_e_2780_);
v_r_2782_ = lean_box(v_res_2781_);
return v_r_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2783_, size_t v_i_2784_, lean_object* v_bs_2785_){
_start:
{
uint8_t v___x_2786_; 
v___x_2786_ = lean_usize_dec_lt(v_i_2784_, v_sz_2783_);
if (v___x_2786_ == 0)
{
return v_bs_2785_;
}
else
{
lean_object* v_v_2787_; lean_object* v_msg_2788_; lean_object* v___x_2789_; lean_object* v_bs_x27_2790_; size_t v___x_2791_; size_t v___x_2792_; lean_object* v___x_2793_; 
v_v_2787_ = lean_array_uget_borrowed(v_bs_2785_, v_i_2784_);
v_msg_2788_ = lean_ctor_get(v_v_2787_, 1);
lean_inc_ref(v_msg_2788_);
v___x_2789_ = lean_unsigned_to_nat(0u);
v_bs_x27_2790_ = lean_array_uset(v_bs_2785_, v_i_2784_, v___x_2789_);
v___x_2791_ = ((size_t)1ULL);
v___x_2792_ = lean_usize_add(v_i_2784_, v___x_2791_);
v___x_2793_ = lean_array_uset(v_bs_x27_2790_, v_i_2784_, v_msg_2788_);
v_i_2784_ = v___x_2792_;
v_bs_2785_ = v___x_2793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2795_, lean_object* v_i_2796_, lean_object* v_bs_2797_){
_start:
{
size_t v_sz_boxed_2798_; size_t v_i_boxed_2799_; lean_object* v_res_2800_; 
v_sz_boxed_2798_ = lean_unbox_usize(v_sz_2795_);
lean_dec(v_sz_2795_);
v_i_boxed_2799_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2798_, v_i_boxed_2799_, v_bs_2797_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2801_, lean_object* v_data_2802_, lean_object* v_ref_2803_, lean_object* v_msg_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_fileName_2808_; lean_object* v_fileMap_2809_; lean_object* v_options_2810_; lean_object* v_currRecDepth_2811_; lean_object* v_maxRecDepth_2812_; lean_object* v_ref_2813_; lean_object* v_currNamespace_2814_; lean_object* v_openDecls_2815_; lean_object* v_initHeartbeats_2816_; lean_object* v_maxHeartbeats_2817_; lean_object* v_quotContext_2818_; lean_object* v_currMacroScope_2819_; uint8_t v_diag_2820_; lean_object* v_cancelTk_x3f_2821_; uint8_t v_suppressElabErrors_2822_; lean_object* v_inheritedTraceOptions_2823_; lean_object* v___x_2824_; lean_object* v_traceState_2825_; lean_object* v_traces_2826_; lean_object* v_ref_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; size_t v_sz_2830_; size_t v___x_2831_; lean_object* v___x_2832_; lean_object* v_msg_2833_; lean_object* v___x_2834_; lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2872_; 
v_fileName_2808_ = lean_ctor_get(v___y_2805_, 0);
v_fileMap_2809_ = lean_ctor_get(v___y_2805_, 1);
v_options_2810_ = lean_ctor_get(v___y_2805_, 2);
v_currRecDepth_2811_ = lean_ctor_get(v___y_2805_, 3);
v_maxRecDepth_2812_ = lean_ctor_get(v___y_2805_, 4);
v_ref_2813_ = lean_ctor_get(v___y_2805_, 5);
v_currNamespace_2814_ = lean_ctor_get(v___y_2805_, 6);
v_openDecls_2815_ = lean_ctor_get(v___y_2805_, 7);
v_initHeartbeats_2816_ = lean_ctor_get(v___y_2805_, 8);
v_maxHeartbeats_2817_ = lean_ctor_get(v___y_2805_, 9);
v_quotContext_2818_ = lean_ctor_get(v___y_2805_, 10);
v_currMacroScope_2819_ = lean_ctor_get(v___y_2805_, 11);
v_diag_2820_ = lean_ctor_get_uint8(v___y_2805_, sizeof(void*)*14);
v_cancelTk_x3f_2821_ = lean_ctor_get(v___y_2805_, 12);
v_suppressElabErrors_2822_ = lean_ctor_get_uint8(v___y_2805_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2823_ = lean_ctor_get(v___y_2805_, 13);
v___x_2824_ = lean_st_ref_get(v___y_2806_);
v_traceState_2825_ = lean_ctor_get(v___x_2824_, 4);
lean_inc_ref(v_traceState_2825_);
lean_dec(v___x_2824_);
v_traces_2826_ = lean_ctor_get(v_traceState_2825_, 0);
lean_inc_ref(v_traces_2826_);
lean_dec_ref(v_traceState_2825_);
v_ref_2827_ = l_Lean_replaceRef(v_ref_2803_, v_ref_2813_);
lean_inc_ref(v_inheritedTraceOptions_2823_);
lean_inc(v_cancelTk_x3f_2821_);
lean_inc(v_currMacroScope_2819_);
lean_inc(v_quotContext_2818_);
lean_inc(v_maxHeartbeats_2817_);
lean_inc(v_initHeartbeats_2816_);
lean_inc(v_openDecls_2815_);
lean_inc(v_currNamespace_2814_);
lean_inc(v_maxRecDepth_2812_);
lean_inc(v_currRecDepth_2811_);
lean_inc_ref(v_options_2810_);
lean_inc_ref(v_fileMap_2809_);
lean_inc_ref(v_fileName_2808_);
v___x_2828_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2828_, 0, v_fileName_2808_);
lean_ctor_set(v___x_2828_, 1, v_fileMap_2809_);
lean_ctor_set(v___x_2828_, 2, v_options_2810_);
lean_ctor_set(v___x_2828_, 3, v_currRecDepth_2811_);
lean_ctor_set(v___x_2828_, 4, v_maxRecDepth_2812_);
lean_ctor_set(v___x_2828_, 5, v_ref_2827_);
lean_ctor_set(v___x_2828_, 6, v_currNamespace_2814_);
lean_ctor_set(v___x_2828_, 7, v_openDecls_2815_);
lean_ctor_set(v___x_2828_, 8, v_initHeartbeats_2816_);
lean_ctor_set(v___x_2828_, 9, v_maxHeartbeats_2817_);
lean_ctor_set(v___x_2828_, 10, v_quotContext_2818_);
lean_ctor_set(v___x_2828_, 11, v_currMacroScope_2819_);
lean_ctor_set(v___x_2828_, 12, v_cancelTk_x3f_2821_);
lean_ctor_set(v___x_2828_, 13, v_inheritedTraceOptions_2823_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*14, v_diag_2820_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*14 + 1, v_suppressElabErrors_2822_);
v___x_2829_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2826_);
lean_dec_ref(v_traces_2826_);
v_sz_2830_ = lean_array_size(v___x_2829_);
v___x_2831_ = ((size_t)0ULL);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2830_, v___x_2831_, v___x_2829_);
v_msg_2833_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2833_, 0, v_data_2802_);
lean_ctor_set(v_msg_2833_, 1, v_msg_2804_);
lean_ctor_set(v_msg_2833_, 2, v___x_2832_);
v___x_2834_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2833_, v___x_2828_, v___y_2806_);
lean_dec_ref_known(v___x_2828_, 14);
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
v___x_2839_ = lean_st_ref_take(v___y_2806_);
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
lean_ctor_set(v___x_2856_, 0, v_ref_2803_);
lean_ctor_set(v___x_2856_, 1, v_a_2835_);
v___x_2857_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2801_, v___x_2856_);
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
v___x_2862_ = lean_st_ref_set(v___y_2806_, v___x_2861_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2873_, lean_object* v_data_2874_, lean_object* v_ref_2875_, lean_object* v_msg_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2873_, v_data_2874_, v_ref_2875_, v_msg_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2880_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2883_ = l_Lean_stringToMessageData(v___x_2882_);
return v___x_2883_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2884_; double v___x_2885_; 
v___x_2884_ = lean_unsigned_to_nat(1000u);
v___x_2885_ = lean_float_of_nat(v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2886_, uint8_t v_collapsed_2887_, lean_object* v_tag_2888_, lean_object* v_opts_2889_, uint8_t v_clsEnabled_2890_, lean_object* v_oldTraces_2891_, lean_object* v_msg_2892_, lean_object* v_resStartStop_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_fst_2897_; lean_object* v_snd_2898_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v_data_2902_; lean_object* v_fst_2913_; lean_object* v_snd_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; lean_object* v___y_2918_; lean_object* v_a_2919_; uint8_t v___y_2934_; double v___y_2965_; 
v_fst_2897_ = lean_ctor_get(v_resStartStop_2893_, 0);
lean_inc(v_fst_2897_);
v_snd_2898_ = lean_ctor_get(v_resStartStop_2893_, 1);
lean_inc(v_snd_2898_);
lean_dec_ref(v_resStartStop_2893_);
v_fst_2913_ = lean_ctor_get(v_snd_2898_, 0);
lean_inc(v_fst_2913_);
v_snd_2914_ = lean_ctor_get(v_snd_2898_, 1);
lean_inc(v_snd_2914_);
lean_dec(v_snd_2898_);
v___x_2915_ = l_Lean_trace_profiler;
v___x_2916_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2889_, v___x_2915_);
if (v___x_2916_ == 0)
{
v___y_2934_ = v___x_2916_;
goto v___jp_2933_;
}
else
{
lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2971_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2889_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; double v___x_2974_; double v___x_2975_; double v___x_2976_; 
v___x_2972_ = l_Lean_trace_profiler_threshold;
v___x_2973_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2889_, v___x_2972_);
v___x_2974_ = lean_float_of_nat(v___x_2973_);
v___x_2975_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_2976_ = lean_float_div(v___x_2974_, v___x_2975_);
v___y_2965_ = v___x_2976_;
goto v___jp_2964_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; double v___x_2979_; 
v___x_2977_ = l_Lean_trace_profiler_threshold;
v___x_2978_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2889_, v___x_2977_);
v___x_2979_ = lean_float_of_nat(v___x_2978_);
v___y_2965_ = v___x_2979_;
goto v___jp_2964_;
}
}
v___jp_2899_:
{
lean_object* v___x_2903_; 
lean_inc(v___y_2901_);
v___x_2903_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2891_, v_data_2902_, v___y_2901_, v___y_2900_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v___x_2904_; 
lean_dec_ref_known(v___x_2903_, 1);
v___x_2904_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2897_);
return v___x_2904_;
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_fst_2897_);
v_a_2905_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2903_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2903_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
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
v___jp_2917_:
{
uint8_t v_result_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; double v___x_2923_; lean_object* v_data_2924_; 
v_result_2920_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2897_);
v___x_2921_ = lean_box(v_result_2920_);
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
v___x_2923_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2888_);
lean_inc_ref(v___x_2922_);
lean_inc(v_cls_2886_);
v_data_2924_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2924_, 0, v_cls_2886_);
lean_ctor_set(v_data_2924_, 1, v___x_2922_);
lean_ctor_set(v_data_2924_, 2, v_tag_2888_);
lean_ctor_set_float(v_data_2924_, sizeof(void*)*3, v___x_2923_);
lean_ctor_set_float(v_data_2924_, sizeof(void*)*3 + 8, v___x_2923_);
lean_ctor_set_uint8(v_data_2924_, sizeof(void*)*3 + 16, v_collapsed_2887_);
if (v___x_2916_ == 0)
{
lean_dec_ref_known(v___x_2922_, 1);
lean_dec(v_snd_2914_);
lean_dec(v_fst_2913_);
lean_dec_ref(v_tag_2888_);
lean_dec(v_cls_2886_);
v___y_2900_ = v_a_2919_;
v___y_2901_ = v___y_2918_;
v_data_2902_ = v_data_2924_;
goto v___jp_2899_;
}
else
{
lean_object* v_data_2925_; double v___x_2926_; double v___x_2927_; 
lean_dec_ref_known(v_data_2924_, 3);
v_data_2925_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2925_, 0, v_cls_2886_);
lean_ctor_set(v_data_2925_, 1, v___x_2922_);
lean_ctor_set(v_data_2925_, 2, v_tag_2888_);
v___x_2926_ = lean_unbox_float(v_fst_2913_);
lean_dec(v_fst_2913_);
lean_ctor_set_float(v_data_2925_, sizeof(void*)*3, v___x_2926_);
v___x_2927_ = lean_unbox_float(v_snd_2914_);
lean_dec(v_snd_2914_);
lean_ctor_set_float(v_data_2925_, sizeof(void*)*3 + 8, v___x_2927_);
lean_ctor_set_uint8(v_data_2925_, sizeof(void*)*3 + 16, v_collapsed_2887_);
v___y_2900_ = v_a_2919_;
v___y_2901_ = v___y_2918_;
v_data_2902_ = v_data_2925_;
goto v___jp_2899_;
}
}
v___jp_2928_:
{
lean_object* v_ref_2929_; lean_object* v___x_2930_; 
v_ref_2929_ = lean_ctor_get(v___y_2894_, 5);
lean_inc(v___y_2895_);
lean_inc_ref(v___y_2894_);
lean_inc(v_fst_2897_);
v___x_2930_ = lean_apply_4(v_msg_2892_, v_fst_2897_, v___y_2894_, v___y_2895_, lean_box(0));
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v___y_2918_ = v_ref_2929_;
v_a_2919_ = v_a_2931_;
goto v___jp_2917_;
}
else
{
lean_object* v___x_2932_; 
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2918_ = v_ref_2929_;
v_a_2919_ = v___x_2932_;
goto v___jp_2917_;
}
}
v___jp_2933_:
{
if (v_clsEnabled_2890_ == 0)
{
if (v___y_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v_traceState_2936_; lean_object* v_env_2937_; lean_object* v_nextMacroScope_2938_; lean_object* v_ngen_2939_; lean_object* v_auxDeclNGen_2940_; lean_object* v_cache_2941_; lean_object* v_messages_2942_; lean_object* v_infoState_2943_; lean_object* v_snapshotTasks_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_snd_2914_);
lean_dec(v_fst_2913_);
lean_dec_ref(v_msg_2892_);
lean_dec_ref(v_tag_2888_);
lean_dec(v_cls_2886_);
v___x_2935_ = lean_st_ref_take(v___y_2895_);
v_traceState_2936_ = lean_ctor_get(v___x_2935_, 4);
v_env_2937_ = lean_ctor_get(v___x_2935_, 0);
v_nextMacroScope_2938_ = lean_ctor_get(v___x_2935_, 1);
v_ngen_2939_ = lean_ctor_get(v___x_2935_, 2);
v_auxDeclNGen_2940_ = lean_ctor_get(v___x_2935_, 3);
v_cache_2941_ = lean_ctor_get(v___x_2935_, 5);
v_messages_2942_ = lean_ctor_get(v___x_2935_, 6);
v_infoState_2943_ = lean_ctor_get(v___x_2935_, 7);
v_snapshotTasks_2944_ = lean_ctor_get(v___x_2935_, 8);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2946_ = v___x_2935_;
v_isShared_2947_ = v_isSharedCheck_2963_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_snapshotTasks_2944_);
lean_inc(v_infoState_2943_);
lean_inc(v_messages_2942_);
lean_inc(v_cache_2941_);
lean_inc(v_traceState_2936_);
lean_inc(v_auxDeclNGen_2940_);
lean_inc(v_ngen_2939_);
lean_inc(v_nextMacroScope_2938_);
lean_inc(v_env_2937_);
lean_dec(v___x_2935_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2963_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint64_t v_tid_2948_; lean_object* v_traces_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2962_; 
v_tid_2948_ = lean_ctor_get_uint64(v_traceState_2936_, sizeof(void*)*1);
v_traces_2949_ = lean_ctor_get(v_traceState_2936_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_traceState_2936_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2951_ = v_traceState_2936_;
v_isShared_2952_ = v_isSharedCheck_2962_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_traces_2949_);
lean_dec(v_traceState_2936_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2962_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2953_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2891_, v_traces_2949_);
lean_dec_ref(v_traces_2949_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2953_);
v___x_2955_ = v___x_2951_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2953_);
lean_ctor_set_uint64(v_reuseFailAlloc_2961_, sizeof(void*)*1, v_tid_2948_);
v___x_2955_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 4, v___x_2955_);
v___x_2957_ = v___x_2946_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_env_2937_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_nextMacroScope_2938_);
lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_ngen_2939_);
lean_ctor_set(v_reuseFailAlloc_2960_, 3, v_auxDeclNGen_2940_);
lean_ctor_set(v_reuseFailAlloc_2960_, 4, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2960_, 5, v_cache_2941_);
lean_ctor_set(v_reuseFailAlloc_2960_, 6, v_messages_2942_);
lean_ctor_set(v_reuseFailAlloc_2960_, 7, v_infoState_2943_);
lean_ctor_set(v_reuseFailAlloc_2960_, 8, v_snapshotTasks_2944_);
v___x_2957_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_st_ref_set(v___y_2895_, v___x_2957_);
v___x_2959_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2897_);
return v___x_2959_;
}
}
}
}
}
else
{
goto v___jp_2928_;
}
}
else
{
goto v___jp_2928_;
}
}
v___jp_2964_:
{
double v___x_2966_; double v___x_2967_; double v___x_2968_; uint8_t v___x_2969_; 
v___x_2966_ = lean_unbox_float(v_snd_2914_);
v___x_2967_ = lean_unbox_float(v_fst_2913_);
v___x_2968_ = lean_float_sub(v___x_2966_, v___x_2967_);
v___x_2969_ = lean_float_decLt(v___y_2965_, v___x_2968_);
v___y_2934_ = v___x_2969_;
goto v___jp_2933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_2980_, lean_object* v_collapsed_2981_, lean_object* v_tag_2982_, lean_object* v_opts_2983_, lean_object* v_clsEnabled_2984_, lean_object* v_oldTraces_2985_, lean_object* v_msg_2986_, lean_object* v_resStartStop_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
uint8_t v_collapsed_boxed_2991_; uint8_t v_clsEnabled_boxed_2992_; lean_object* v_res_2993_; 
v_collapsed_boxed_2991_ = lean_unbox(v_collapsed_2981_);
v_clsEnabled_boxed_2992_ = lean_unbox(v_clsEnabled_2984_);
v_res_2993_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_2980_, v_collapsed_boxed_2991_, v_tag_2982_, v_opts_2983_, v_clsEnabled_boxed_2992_, v_oldTraces_2985_, v_msg_2986_, v_resStartStop_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v_opts_2983_);
return v_res_2993_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
lean_ctor_set(v___x_2998_, 2, v___x_2997_);
lean_ctor_set(v___x_2998_, 3, v___x_2997_);
lean_ctor_set(v___x_2998_, 4, v___x_2996_);
lean_ctor_set(v___x_2998_, 5, v___x_2996_);
lean_ctor_set(v___x_2998_, 6, v___x_2996_);
lean_ctor_set(v___x_2998_, 7, v___x_2996_);
lean_ctor_set(v___x_2998_, 8, v___x_2996_);
lean_ctor_set(v___x_2998_, 9, v___x_2996_);
return v___x_2998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3000_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
lean_ctor_set(v___x_3000_, 2, v___x_2999_);
lean_ctor_set(v___x_3000_, 3, v___x_2999_);
lean_ctor_set(v___x_3000_, 4, v___x_2999_);
lean_ctor_set(v___x_3000_, 5, v___x_2999_);
return v___x_3000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_3002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
lean_ctor_set(v___x_3002_, 2, v___x_3001_);
lean_ctor_set(v___x_3002_, 3, v___x_3001_);
lean_ctor_set(v___x_3002_, 4, v___x_3001_);
return v___x_3002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3003_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3004_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3005_ = lean_box(1);
v___x_3006_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3007_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___x_3006_);
lean_ctor_set(v___x_3008_, 2, v___x_3005_);
lean_ctor_set(v___x_3008_, 3, v___x_3004_);
lean_ctor_set(v___x_3008_, 4, v___x_3003_);
return v___x_3008_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3014_ = l_Lean_Name_append(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3015_; double v___x_3016_; 
v___x_3015_ = lean_unsigned_to_nat(1000000000u);
v___x_3016_ = lean_float_of_nat(v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___f_3017_, lean_object* v_name_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_options_3022_; uint8_t v_hasTrace_3023_; 
v_options_3022_ = lean_ctor_get(v___y_3019_, 2);
v_hasTrace_3023_ = lean_ctor_get_uint8(v_options_3022_, sizeof(void*)*1);
if (v_hasTrace_3023_ == 0)
{
lean_object* v___x_3024_; lean_object* v_env_3025_; lean_object* v___x_3026_; 
lean_dec_ref(v___f_3017_);
v___x_3024_ = lean_st_ref_get(v___y_3020_);
v_env_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc_ref(v_env_3025_);
lean_dec(v___x_3024_);
lean_inc(v_name_3018_);
v___x_3026_ = l_Lean_Meta_declFromEqLikeName(v_env_3025_, v_name_3018_);
if (lean_obj_tag(v___x_3026_) == 1)
{
lean_object* v_val_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3126_; 
v_val_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3126_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_val_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3126_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v_fst_3031_; lean_object* v_snd_3032_; lean_object* v___x_3033_; lean_object* v_env_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_fst_3031_ = lean_ctor_get(v_val_3027_, 0);
lean_inc_n(v_fst_3031_, 2);
v_snd_3032_ = lean_ctor_get(v_val_3027_, 1);
lean_inc_n(v_snd_3032_, 2);
lean_dec(v_val_3027_);
v___x_3033_ = lean_st_ref_get(v___y_3020_);
v_env_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc_ref(v_env_3034_);
lean_dec(v___x_3033_);
v___x_3035_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3034_, v_fst_3031_, v_snd_3032_);
v___x_3036_ = lean_name_eq(v_name_3018_, v___x_3035_);
lean_dec(v___x_3035_);
lean_dec(v_name_3018_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec(v_snd_3032_);
lean_dec(v_fst_3031_);
v___x_3037_ = lean_box(v_hasTrace_3023_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set_tag(v___x_3029_, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3037_);
v___x_3039_ = v___x_3029_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
else
{
uint8_t v___x_3041_; lean_object* v_a_3043_; 
lean_inc(v_snd_3032_);
v___x_3041_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3032_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v_a_3060_; 
lean_del_object(v___x_3029_);
v___x_3057_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3058_ = lean_string_dec_eq(v_snd_3032_, v___x_3057_);
lean_dec(v_snd_3032_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_dec(v_fst_3031_);
v___x_3072_ = lean_box(v_hasTrace_3023_);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
return v___x_3073_;
}
else
{
uint8_t v___x_3074_; uint8_t v___x_3075_; uint8_t v___x_3076_; lean_object* v___x_3077_; uint64_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3074_ = 1;
v___x_3075_ = 0;
v___x_3076_ = 2;
v___x_3077_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3077_, 0, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3077_, 1, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3077_, 2, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3077_, 3, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3077_, 4, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3077_, 5, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 6, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 7, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3077_, 8, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 9, v___x_3074_);
lean_ctor_set_uint8(v___x_3077_, 10, v___x_3075_);
lean_ctor_set_uint8(v___x_3077_, 11, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 12, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 13, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 14, v___x_3076_);
lean_ctor_set_uint8(v___x_3077_, 15, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 16, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 17, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 18, v___x_3058_);
lean_ctor_set_uint8(v___x_3077_, 19, v_hasTrace_3023_);
v___x_3078_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3079_, 0, v___x_3077_);
lean_ctor_set_uint64(v___x_3079_, sizeof(void*)*1, v___x_3078_);
v___x_3080_ = lean_box(1);
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3083_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3085_, 0, v___x_3079_);
lean_ctor_set(v___x_3085_, 1, v___x_3080_);
lean_ctor_set(v___x_3085_, 2, v___x_3082_);
lean_ctor_set(v___x_3085_, 3, v___x_3083_);
lean_ctor_set(v___x_3085_, 4, v___x_3084_);
lean_ctor_set(v___x_3085_, 5, v___x_3081_);
lean_ctor_set(v___x_3085_, 6, v___x_3084_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*7, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*7 + 1, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*7 + 2, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*7 + 3, v___x_3036_);
v___x_3086_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3087_ = lean_st_mk_ref(v___x_3086_);
v___x_3088_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3031_, v___x_3036_, v___x_3085_, v___x_3087_, v___y_3019_, v___y_3020_);
lean_dec_ref_known(v___x_3085_, 7);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3090_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3090_ = lean_st_ref_get(v___x_3087_);
lean_dec(v___x_3087_);
lean_dec(v___x_3090_);
v_a_3060_ = v_a_3089_;
goto v___jp_3059_;
}
else
{
lean_dec(v___x_3087_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3091_; 
v_a_3091_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3088_, 1);
v_a_3060_ = v_a_3091_;
goto v___jp_3059_;
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
v_a_3092_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3088_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3088_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
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
v___jp_3059_:
{
if (lean_obj_tag(v_a_3060_) == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_box(v_hasTrace_3023_);
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
return v___x_3062_;
}
else
{
lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3070_; 
v_isSharedCheck_3070_ = !lean_is_exclusive(v_a_3060_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v_a_3060_, 0);
lean_dec(v_unused_3071_);
v___x_3064_ = v_a_3060_;
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
else
{
lean_dec(v_a_3060_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3070_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3066_ = lean_box(v___x_3058_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set_tag(v___x_3064_, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3066_);
v___x_3068_ = v___x_3064_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
else
{
uint8_t v___x_3100_; uint8_t v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; uint64_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v_snd_3032_);
v___x_3100_ = 1;
v___x_3101_ = 0;
v___x_3102_ = 2;
v___x_3103_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3103_, 0, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3103_, 1, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3103_, 2, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3103_, 3, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3103_, 4, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3103_, 5, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 6, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 7, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3103_, 8, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 9, v___x_3100_);
lean_ctor_set_uint8(v___x_3103_, 10, v___x_3101_);
lean_ctor_set_uint8(v___x_3103_, 11, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 12, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 13, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 14, v___x_3102_);
lean_ctor_set_uint8(v___x_3103_, 15, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 16, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 17, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 18, v___x_3041_);
lean_ctor_set_uint8(v___x_3103_, 19, v_hasTrace_3023_);
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
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 1, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 2, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 3, v___x_3036_);
v___x_3112_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3113_ = lean_st_mk_ref(v___x_3112_);
v___x_3114_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3031_, v___x_3111_, v___x_3113_, v___y_3019_, v___y_3020_);
lean_dec_ref_known(v___x_3111_, 7);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = lean_st_ref_get(v___x_3113_);
lean_dec(v___x_3113_);
lean_dec(v___x_3116_);
v_a_3043_ = v_a_3115_;
goto v___jp_3042_;
}
else
{
lean_dec(v___x_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3117_; 
v_a_3117_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3114_, 1);
v_a_3043_ = v_a_3117_;
goto v___jp_3042_;
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_del_object(v___x_3029_);
v_a_3118_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3114_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3114_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
v___jp_3042_:
{
if (lean_obj_tag(v_a_3043_) == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3044_ = lean_box(v_hasTrace_3023_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set_tag(v___x_3029_, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3044_);
v___x_3046_ = v___x_3029_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
else
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3055_; 
lean_del_object(v___x_3029_);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_a_3043_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; 
v_unused_3056_ = lean_ctor_get(v_a_3043_, 0);
lean_dec(v_unused_3056_);
v___x_3049_ = v_a_3043_;
v_isShared_3050_ = v_isSharedCheck_3055_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v_a_3043_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3055_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3051_ = lean_box(v___x_3041_);
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
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec(v___x_3026_);
lean_dec(v_name_3018_);
v___x_3127_ = lean_box(v_hasTrace_3023_);
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3129_; lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v_a_3138_; lean_object* v___y_3151_; lean_object* v___y_3152_; uint8_t v_a_3153_; lean_object* v___y_3157_; uint8_t v___y_3158_; lean_object* v___y_3159_; lean_object* v_a_3160_; lean_object* v___y_3162_; uint8_t v___y_3163_; lean_object* v___y_3164_; lean_object* v_a_3165_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v_a_3169_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v_a_3174_; lean_object* v___y_3184_; lean_object* v___y_3185_; uint8_t v_a_3186_; lean_object* v___y_3190_; lean_object* v___y_3191_; uint8_t v___y_3192_; uint8_t v___y_3193_; lean_object* v_a_3194_; lean_object* v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3198_; lean_object* v_a_3199_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v_a_3204_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; 
v_inheritedTraceOptions_3129_ = lean_ctor_get(v___y_3019_, 13);
lean_inc(v_name_3018_);
v___f_3130_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3130_, 0, v_name_3018_);
v___x_3131_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3132_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3133_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3129_, v_options_3022_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3329_; uint8_t v___x_3330_; lean_object* v_a_3332_; lean_object* v_a_3345_; 
v___x_3329_ = l_Lean_trace_profiler;
v___x_3330_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3022_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3357_; lean_object* v_env_3358_; lean_object* v___x_3359_; 
lean_dec_ref(v___f_3130_);
lean_dec_ref(v___f_3017_);
v___x_3357_ = lean_st_ref_get(v___y_3020_);
v_env_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc_ref(v_env_3358_);
lean_dec(v___x_3357_);
lean_inc(v_name_3018_);
v___x_3359_ = l_Lean_Meta_declFromEqLikeName(v_env_3358_, v_name_3018_);
if (lean_obj_tag(v___x_3359_) == 1)
{
lean_object* v_val_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3433_; 
v_val_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3433_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_val_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3433_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v_fst_3364_; lean_object* v_snd_3365_; lean_object* v___x_3366_; lean_object* v_env_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_fst_3364_ = lean_ctor_get(v_val_3360_, 0);
lean_inc_n(v_fst_3364_, 2);
v_snd_3365_ = lean_ctor_get(v_val_3360_, 1);
lean_inc_n(v_snd_3365_, 2);
lean_dec(v_val_3360_);
v___x_3366_ = lean_st_ref_get(v___y_3020_);
v_env_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc_ref(v_env_3367_);
lean_dec(v___x_3366_);
v___x_3368_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3367_, v_fst_3364_, v_snd_3365_);
v___x_3369_ = lean_name_eq(v_name_3018_, v___x_3368_);
lean_dec(v___x_3368_);
lean_dec(v_name_3018_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
lean_dec(v_snd_3365_);
lean_dec(v_fst_3364_);
v___x_3370_ = lean_box(v___x_3330_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3370_);
v___x_3372_ = v___x_3362_;
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
else
{
uint8_t v___x_3374_; 
lean_inc(v_snd_3365_);
v___x_3374_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3365_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; uint8_t v___x_3376_; 
v___x_3375_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3376_ = lean_string_dec_eq(v_snd_3365_, v___x_3375_);
lean_dec(v_snd_3365_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3379_; 
lean_dec(v_fst_3364_);
v___x_3377_ = lean_box(v___x_3330_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3377_);
v___x_3379_ = v___x_3362_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
else
{
uint8_t v___x_3381_; uint8_t v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; uint64_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_del_object(v___x_3362_);
v___x_3381_ = 1;
v___x_3382_ = 0;
v___x_3383_ = 2;
v___x_3384_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3384_, 0, v___x_3330_);
lean_ctor_set_uint8(v___x_3384_, 1, v___x_3330_);
lean_ctor_set_uint8(v___x_3384_, 2, v___x_3330_);
lean_ctor_set_uint8(v___x_3384_, 3, v___x_3330_);
lean_ctor_set_uint8(v___x_3384_, 4, v___x_3330_);
lean_ctor_set_uint8(v___x_3384_, 5, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 6, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 7, v___x_3330_);
lean_ctor_set_uint8(v___x_3384_, 8, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 9, v___x_3381_);
lean_ctor_set_uint8(v___x_3384_, 10, v___x_3382_);
lean_ctor_set_uint8(v___x_3384_, 11, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 12, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 13, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 14, v___x_3383_);
lean_ctor_set_uint8(v___x_3384_, 15, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 16, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 17, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 18, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3384_, 19, v___x_3330_);
v___x_3385_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3384_);
v___x_3386_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set_uint64(v___x_3386_, sizeof(void*)*1, v___x_3385_);
v___x_3387_ = lean_box(1);
v___x_3388_ = lean_unsigned_to_nat(0u);
v___x_3389_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3391_ = lean_box(0);
v___x_3392_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3392_, 0, v___x_3386_);
lean_ctor_set(v___x_3392_, 1, v___x_3387_);
lean_ctor_set(v___x_3392_, 2, v___x_3389_);
lean_ctor_set(v___x_3392_, 3, v___x_3390_);
lean_ctor_set(v___x_3392_, 4, v___x_3391_);
lean_ctor_set(v___x_3392_, 5, v___x_3388_);
lean_ctor_set(v___x_3392_, 6, v___x_3391_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*7, v___x_3330_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*7 + 1, v___x_3330_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*7 + 2, v___x_3330_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*7 + 3, v_hasTrace_3023_);
v___x_3393_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3394_ = lean_st_mk_ref(v___x_3393_);
v___x_3395_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3364_, v_hasTrace_3023_, v___x_3392_, v___x_3394_, v___y_3019_, v___y_3020_);
lean_dec_ref_known(v___x_3392_, 7);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3397_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3395_, 1);
v___x_3397_ = lean_st_ref_get(v___x_3394_);
lean_dec(v___x_3394_);
lean_dec(v___x_3397_);
v_a_3345_ = v_a_3396_;
goto v___jp_3344_;
}
else
{
lean_dec(v___x_3394_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3398_; 
v_a_3398_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3395_, 1);
v_a_3345_ = v_a_3398_;
goto v___jp_3344_;
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
v_a_3399_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3395_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3395_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
}
else
{
uint8_t v___x_3407_; uint8_t v___x_3408_; uint8_t v___x_3409_; lean_object* v___x_3410_; uint64_t v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_dec(v_snd_3365_);
lean_del_object(v___x_3362_);
v___x_3407_ = 1;
v___x_3408_ = 0;
v___x_3409_ = 2;
v___x_3410_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3410_, 0, v___x_3330_);
lean_ctor_set_uint8(v___x_3410_, 1, v___x_3330_);
lean_ctor_set_uint8(v___x_3410_, 2, v___x_3330_);
lean_ctor_set_uint8(v___x_3410_, 3, v___x_3330_);
lean_ctor_set_uint8(v___x_3410_, 4, v___x_3330_);
lean_ctor_set_uint8(v___x_3410_, 5, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 6, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 7, v___x_3330_);
lean_ctor_set_uint8(v___x_3410_, 8, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 9, v___x_3407_);
lean_ctor_set_uint8(v___x_3410_, 10, v___x_3408_);
lean_ctor_set_uint8(v___x_3410_, 11, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 12, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 13, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 14, v___x_3409_);
lean_ctor_set_uint8(v___x_3410_, 15, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 16, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 17, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 18, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3410_, 19, v___x_3330_);
v___x_3411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3410_);
v___x_3412_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3412_, 0, v___x_3410_);
lean_ctor_set_uint64(v___x_3412_, sizeof(void*)*1, v___x_3411_);
v___x_3413_ = lean_box(1);
v___x_3414_ = lean_unsigned_to_nat(0u);
v___x_3415_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3416_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3417_ = lean_box(0);
v___x_3418_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3418_, 0, v___x_3412_);
lean_ctor_set(v___x_3418_, 1, v___x_3413_);
lean_ctor_set(v___x_3418_, 2, v___x_3415_);
lean_ctor_set(v___x_3418_, 3, v___x_3416_);
lean_ctor_set(v___x_3418_, 4, v___x_3417_);
lean_ctor_set(v___x_3418_, 5, v___x_3414_);
lean_ctor_set(v___x_3418_, 6, v___x_3417_);
lean_ctor_set_uint8(v___x_3418_, sizeof(void*)*7, v___x_3330_);
lean_ctor_set_uint8(v___x_3418_, sizeof(void*)*7 + 1, v___x_3330_);
lean_ctor_set_uint8(v___x_3418_, sizeof(void*)*7 + 2, v___x_3330_);
lean_ctor_set_uint8(v___x_3418_, sizeof(void*)*7 + 3, v_hasTrace_3023_);
v___x_3419_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3420_ = lean_st_mk_ref(v___x_3419_);
v___x_3421_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3364_, v___x_3418_, v___x_3420_, v___y_3019_, v___y_3020_);
lean_dec_ref_known(v___x_3418_, 7);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = lean_st_ref_get(v___x_3420_);
lean_dec(v___x_3420_);
lean_dec(v___x_3423_);
v_a_3332_ = v_a_3422_;
goto v___jp_3331_;
}
else
{
lean_dec(v___x_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3424_; 
v_a_3424_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3421_, 1);
v_a_3332_ = v_a_3424_;
goto v___jp_3331_;
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
v_a_3425_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3421_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3421_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
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
lean_object* v___x_3434_; lean_object* v___x_3435_; 
lean_dec(v___x_3359_);
lean_dec(v_name_3018_);
v___x_3434_ = lean_box(v___x_3330_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
}
else
{
goto v___jp_3213_;
}
v___jp_3331_:
{
if (lean_obj_tag(v_a_3332_) == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_box(v___x_3330_);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
else
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3342_; 
v_isSharedCheck_3342_ = !lean_is_exclusive(v_a_3332_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; 
v_unused_3343_ = lean_ctor_get(v_a_3332_, 0);
lean_dec(v_unused_3343_);
v___x_3336_ = v_a_3332_;
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v_a_3332_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3338_ = lean_box(v_hasTrace_3023_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
v___jp_3344_:
{
if (lean_obj_tag(v_a_3345_) == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_box(v___x_3330_);
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
}
else
{
lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3355_; 
v_isSharedCheck_3355_ = !lean_is_exclusive(v_a_3345_);
if (v_isSharedCheck_3355_ == 0)
{
lean_object* v_unused_3356_; 
v_unused_3356_ = lean_ctor_get(v_a_3345_, 0);
lean_dec(v_unused_3356_);
v___x_3349_ = v_a_3345_;
v_isShared_3350_ = v_isSharedCheck_3355_;
goto v_resetjp_3348_;
}
else
{
lean_dec(v_a_3345_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3355_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3351_ = lean_box(v_hasTrace_3023_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set_tag(v___x_3349_, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3351_);
v___x_3353_ = v___x_3349_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
else
{
goto v___jp_3213_;
}
v___jp_3135_:
{
lean_object* v___x_3139_; double v___x_3140_; double v___x_3141_; double v___x_3142_; double v___x_3143_; double v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3139_ = lean_io_mono_nanos_now();
v___x_3140_ = lean_float_of_nat(v___y_3137_);
v___x_3141_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3142_ = lean_float_div(v___x_3140_, v___x_3141_);
v___x_3143_ = lean_float_of_nat(v___x_3139_);
v___x_3144_ = lean_float_div(v___x_3143_, v___x_3141_);
v___x_3145_ = lean_box_float(v___x_3142_);
v___x_3146_ = lean_box_float(v___x_3144_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_a_3138_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3131_, v_hasTrace_3023_, v___x_3132_, v_options_3022_, v___x_3134_, v___y_3136_, v___f_3130_, v___x_3148_, v___y_3019_, v___y_3020_);
return v___x_3149_;
}
v___jp_3150_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_box(v_a_3153_);
v___x_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
v___y_3136_ = v___y_3151_;
v___y_3137_ = v___y_3152_;
v_a_3138_ = v___x_3155_;
goto v___jp_3135_;
}
v___jp_3156_:
{
if (lean_obj_tag(v_a_3160_) == 0)
{
v___y_3151_ = v___y_3157_;
v___y_3152_ = v___y_3159_;
v_a_3153_ = v___y_3158_;
goto v___jp_3150_;
}
else
{
lean_dec_ref_known(v_a_3160_, 1);
v___y_3151_ = v___y_3157_;
v___y_3152_ = v___y_3159_;
v_a_3153_ = v_hasTrace_3023_;
goto v___jp_3150_;
}
}
v___jp_3161_:
{
if (lean_obj_tag(v_a_3165_) == 0)
{
v___y_3151_ = v___y_3162_;
v___y_3152_ = v___y_3164_;
v_a_3153_ = v___y_3163_;
goto v___jp_3150_;
}
else
{
lean_dec_ref_known(v_a_3165_, 1);
v___y_3151_ = v___y_3162_;
v___y_3152_ = v___y_3164_;
v_a_3153_ = v_hasTrace_3023_;
goto v___jp_3150_;
}
}
v___jp_3166_:
{
lean_object* v___x_3170_; 
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v_a_3169_);
v___y_3136_ = v___y_3167_;
v___y_3137_ = v___y_3168_;
v_a_3138_ = v___x_3170_;
goto v___jp_3135_;
}
v___jp_3171_:
{
lean_object* v___x_3175_; double v___x_3176_; double v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3175_ = lean_io_get_num_heartbeats();
v___x_3176_ = lean_float_of_nat(v___y_3172_);
v___x_3177_ = lean_float_of_nat(v___x_3175_);
v___x_3178_ = lean_box_float(v___x_3176_);
v___x_3179_ = lean_box_float(v___x_3177_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_a_3174_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3131_, v_hasTrace_3023_, v___x_3132_, v_options_3022_, v___x_3134_, v___y_3173_, v___f_3130_, v___x_3181_, v___y_3019_, v___y_3020_);
return v___x_3182_;
}
v___jp_3183_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_box(v_a_3186_);
v___x_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
v___y_3172_ = v___y_3184_;
v___y_3173_ = v___y_3185_;
v_a_3174_ = v___x_3188_;
goto v___jp_3171_;
}
v___jp_3189_:
{
if (lean_obj_tag(v_a_3194_) == 0)
{
v___y_3184_ = v___y_3190_;
v___y_3185_ = v___y_3191_;
v_a_3186_ = v___y_3193_;
goto v___jp_3183_;
}
else
{
lean_dec_ref_known(v_a_3194_, 1);
v___y_3184_ = v___y_3190_;
v___y_3185_ = v___y_3191_;
v_a_3186_ = v___y_3192_;
goto v___jp_3183_;
}
}
v___jp_3195_:
{
if (lean_obj_tag(v_a_3199_) == 0)
{
uint8_t v___x_3200_; 
v___x_3200_ = 0;
v___y_3184_ = v___y_3196_;
v___y_3185_ = v___y_3197_;
v_a_3186_ = v___x_3200_;
goto v___jp_3183_;
}
else
{
lean_dec_ref_known(v_a_3199_, 1);
v___y_3184_ = v___y_3196_;
v___y_3185_ = v___y_3197_;
v_a_3186_ = v___y_3198_;
goto v___jp_3183_;
}
}
v___jp_3201_:
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v_a_3204_);
v___y_3172_ = v___y_3202_;
v___y_3173_ = v___y_3203_;
v_a_3174_ = v___x_3205_;
goto v___jp_3171_;
}
v___jp_3206_:
{
if (lean_obj_tag(v___y_3209_) == 0)
{
lean_object* v_a_3210_; uint8_t v___x_3211_; 
v_a_3210_ = lean_ctor_get(v___y_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___y_3209_, 1);
v___x_3211_ = lean_unbox(v_a_3210_);
lean_dec(v_a_3210_);
v___y_3184_ = v___y_3207_;
v___y_3185_ = v___y_3208_;
v_a_3186_ = v___x_3211_;
goto v___jp_3183_;
}
else
{
lean_object* v_a_3212_; 
v_a_3212_ = lean_ctor_get(v___y_3209_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___y_3209_, 1);
v___y_3202_ = v___y_3207_;
v___y_3203_ = v___y_3208_;
v_a_3204_ = v_a_3212_;
goto v___jp_3201_;
}
}
v___jp_3213_:
{
lean_object* v___x_3214_; lean_object* v_a_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3214_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3020_);
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref(v___x_3214_);
v___x_3216_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3217_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3022_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v_env_3220_; lean_object* v___x_3221_; 
lean_dec_ref(v___f_3017_);
v___x_3218_ = lean_io_mono_nanos_now();
v___x_3219_ = lean_st_ref_get(v___y_3020_);
v_env_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc_ref(v_env_3220_);
lean_dec(v___x_3219_);
lean_inc(v_name_3018_);
v___x_3221_ = l_Lean_Meta_declFromEqLikeName(v_env_3220_, v_name_3018_);
if (lean_obj_tag(v___x_3221_) == 1)
{
lean_object* v_val_3222_; lean_object* v_fst_3223_; lean_object* v_snd_3224_; lean_object* v___x_3225_; lean_object* v_env_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v_val_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_val_3222_);
lean_dec_ref_known(v___x_3221_, 1);
v_fst_3223_ = lean_ctor_get(v_val_3222_, 0);
lean_inc_n(v_fst_3223_, 2);
v_snd_3224_ = lean_ctor_get(v_val_3222_, 1);
lean_inc_n(v_snd_3224_, 2);
lean_dec(v_val_3222_);
v___x_3225_ = lean_st_ref_get(v___y_3020_);
v_env_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc_ref(v_env_3226_);
lean_dec(v___x_3225_);
v___x_3227_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3226_, v_fst_3223_, v_snd_3224_);
v___x_3228_ = lean_name_eq(v_name_3018_, v___x_3227_);
lean_dec(v___x_3227_);
lean_dec(v_name_3018_);
if (v___x_3228_ == 0)
{
lean_dec(v_snd_3224_);
lean_dec(v_fst_3223_);
v___y_3151_ = v_a_3215_;
v___y_3152_ = v___x_3218_;
v_a_3153_ = v___x_3217_;
goto v___jp_3150_;
}
else
{
uint8_t v___x_3229_; 
lean_inc(v_snd_3224_);
v___x_3229_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3224_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3231_ = lean_string_dec_eq(v_snd_3224_, v___x_3230_);
lean_dec(v_snd_3224_);
if (v___x_3231_ == 0)
{
lean_dec(v_fst_3223_);
v___y_3151_ = v_a_3215_;
v___y_3152_ = v___x_3218_;
v_a_3153_ = v___x_3217_;
goto v___jp_3150_;
}
else
{
uint8_t v___x_3232_; uint8_t v___x_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; uint64_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3232_ = 1;
v___x_3233_ = 0;
v___x_3234_ = 2;
v___x_3235_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3235_, 0, v___x_3217_);
lean_ctor_set_uint8(v___x_3235_, 1, v___x_3217_);
lean_ctor_set_uint8(v___x_3235_, 2, v___x_3217_);
lean_ctor_set_uint8(v___x_3235_, 3, v___x_3217_);
lean_ctor_set_uint8(v___x_3235_, 4, v___x_3217_);
lean_ctor_set_uint8(v___x_3235_, 5, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 6, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 7, v___x_3217_);
lean_ctor_set_uint8(v___x_3235_, 8, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 9, v___x_3232_);
lean_ctor_set_uint8(v___x_3235_, 10, v___x_3233_);
lean_ctor_set_uint8(v___x_3235_, 11, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 12, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 13, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 14, v___x_3234_);
lean_ctor_set_uint8(v___x_3235_, 15, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 16, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 17, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 18, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3235_, 19, v___x_3217_);
v___x_3236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3235_);
v___x_3237_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set_uint64(v___x_3237_, sizeof(void*)*1, v___x_3236_);
v___x_3238_ = lean_box(1);
v___x_3239_ = lean_unsigned_to_nat(0u);
v___x_3240_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3241_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3242_ = lean_box(0);
v___x_3243_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3243_, 0, v___x_3237_);
lean_ctor_set(v___x_3243_, 1, v___x_3238_);
lean_ctor_set(v___x_3243_, 2, v___x_3240_);
lean_ctor_set(v___x_3243_, 3, v___x_3241_);
lean_ctor_set(v___x_3243_, 4, v___x_3242_);
lean_ctor_set(v___x_3243_, 5, v___x_3239_);
lean_ctor_set(v___x_3243_, 6, v___x_3242_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7, v___x_3217_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 1, v___x_3217_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 2, v___x_3217_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 3, v_hasTrace_3023_);
v___x_3244_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3245_ = lean_st_mk_ref(v___x_3244_);
v___x_3246_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3223_, v_hasTrace_3023_, v___x_3243_, v___x_3245_, v___y_3019_, v___y_3020_);
lean_dec_ref_known(v___x_3243_, 7);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3248_ = lean_st_ref_get(v___x_3245_);
lean_dec(v___x_3245_);
lean_dec(v___x_3248_);
v___y_3162_ = v_a_3215_;
v___y_3163_ = v___x_3217_;
v___y_3164_ = v___x_3218_;
v_a_3165_ = v_a_3247_;
goto v___jp_3161_;
}
else
{
lean_dec(v___x_3245_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3249_; 
v_a_3249_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3246_, 1);
v___y_3162_ = v_a_3215_;
v___y_3163_ = v___x_3217_;
v___y_3164_ = v___x_3218_;
v_a_3165_ = v_a_3249_;
goto v___jp_3161_;
}
else
{
lean_object* v_a_3250_; 
v_a_3250_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3246_, 1);
v___y_3167_ = v_a_3215_;
v___y_3168_ = v___x_3218_;
v_a_3169_ = v_a_3250_;
goto v___jp_3166_;
}
}
}
}
else
{
uint8_t v___x_3251_; uint8_t v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; uint64_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec(v_snd_3224_);
v___x_3251_ = 1;
v___x_3252_ = 0;
v___x_3253_ = 2;
v___x_3254_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3254_, 0, v___x_3217_);
lean_ctor_set_uint8(v___x_3254_, 1, v___x_3217_);
lean_ctor_set_uint8(v___x_3254_, 2, v___x_3217_);
lean_ctor_set_uint8(v___x_3254_, 3, v___x_3217_);
lean_ctor_set_uint8(v___x_3254_, 4, v___x_3217_);
lean_ctor_set_uint8(v___x_3254_, 5, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 6, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 7, v___x_3217_);
lean_ctor_set_uint8(v___x_3254_, 8, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 9, v___x_3251_);
lean_ctor_set_uint8(v___x_3254_, 10, v___x_3252_);
lean_ctor_set_uint8(v___x_3254_, 11, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 12, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 13, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 14, v___x_3253_);
lean_ctor_set_uint8(v___x_3254_, 15, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 16, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 17, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 18, v_hasTrace_3023_);
lean_ctor_set_uint8(v___x_3254_, 19, v___x_3217_);
v___x_3255_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3254_);
v___x_3256_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set_uint64(v___x_3256_, sizeof(void*)*1, v___x_3255_);
v___x_3257_ = lean_box(1);
v___x_3258_ = lean_unsigned_to_nat(0u);
v___x_3259_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3260_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3262_, 0, v___x_3256_);
lean_ctor_set(v___x_3262_, 1, v___x_3257_);
lean_ctor_set(v___x_3262_, 2, v___x_3259_);
lean_ctor_set(v___x_3262_, 3, v___x_3260_);
lean_ctor_set(v___x_3262_, 4, v___x_3261_);
lean_ctor_set(v___x_3262_, 5, v___x_3258_);
lean_ctor_set(v___x_3262_, 6, v___x_3261_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*7, v___x_3217_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*7 + 1, v___x_3217_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*7 + 2, v___x_3217_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*7 + 3, v_hasTrace_3023_);
v___x_3263_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3264_ = lean_st_mk_ref(v___x_3263_);
v___x_3265_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3223_, v___x_3262_, v___x_3264_, v___y_3019_, v___y_3020_);
lean_dec_ref_known(v___x_3262_, 7);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = lean_st_ref_get(v___x_3264_);
lean_dec(v___x_3264_);
lean_dec(v___x_3267_);
v___y_3157_ = v_a_3215_;
v___y_3158_ = v___x_3217_;
v___y_3159_ = v___x_3218_;
v_a_3160_ = v_a_3266_;
goto v___jp_3156_;
}
else
{
lean_dec(v___x_3264_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3268_; 
v_a_3268_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3265_, 1);
v___y_3157_ = v_a_3215_;
v___y_3158_ = v___x_3217_;
v___y_3159_ = v___x_3218_;
v_a_3160_ = v_a_3268_;
goto v___jp_3156_;
}
else
{
lean_object* v_a_3269_; 
v_a_3269_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3265_, 1);
v___y_3167_ = v_a_3215_;
v___y_3168_ = v___x_3218_;
v_a_3169_ = v_a_3269_;
goto v___jp_3166_;
}
}
}
}
}
else
{
lean_dec(v___x_3221_);
lean_dec(v_name_3018_);
v___y_3151_ = v_a_3215_;
v___y_3152_ = v___x_3218_;
v_a_3153_ = v___x_3217_;
goto v___jp_3150_;
}
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v_env_3272_; lean_object* v___x_3273_; 
v___x_3270_ = lean_io_get_num_heartbeats();
v___x_3271_ = lean_st_ref_get(v___y_3020_);
v_env_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc_ref(v_env_3272_);
lean_dec(v___x_3271_);
lean_inc(v_name_3018_);
v___x_3273_ = l_Lean_Meta_declFromEqLikeName(v_env_3272_, v_name_3018_);
if (lean_obj_tag(v___x_3273_) == 1)
{
lean_object* v_val_3274_; lean_object* v_fst_3275_; lean_object* v_snd_3276_; lean_object* v___x_3277_; lean_object* v_env_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v_val_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_val_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v_fst_3275_ = lean_ctor_get(v_val_3274_, 0);
lean_inc_n(v_fst_3275_, 2);
v_snd_3276_ = lean_ctor_get(v_val_3274_, 1);
lean_inc_n(v_snd_3276_, 2);
lean_dec(v_val_3274_);
v___x_3277_ = lean_st_ref_get(v___y_3020_);
v_env_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc_ref(v_env_3278_);
lean_dec(v___x_3277_);
v___x_3279_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3278_, v_fst_3275_, v_snd_3276_);
v___x_3280_ = lean_name_eq(v_name_3018_, v___x_3279_);
lean_dec(v___x_3279_);
lean_dec(v_name_3018_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec(v_snd_3276_);
lean_dec(v_fst_3275_);
v___x_3281_ = lean_box(0);
lean_inc(v___y_3020_);
lean_inc_ref(v___y_3019_);
v___x_3282_ = lean_apply_4(v___f_3017_, v___x_3281_, v___y_3019_, v___y_3020_, lean_box(0));
v___y_3207_ = v___x_3270_;
v___y_3208_ = v_a_3215_;
v___y_3209_ = v___x_3282_;
goto v___jp_3206_;
}
else
{
uint8_t v___x_3283_; 
lean_inc(v_snd_3276_);
v___x_3283_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3276_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3285_ = lean_string_dec_eq(v_snd_3276_, v___x_3284_);
lean_dec(v_snd_3276_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_dec(v_fst_3275_);
v___x_3286_ = lean_box(0);
lean_inc(v___y_3020_);
lean_inc_ref(v___y_3019_);
v___x_3287_ = lean_apply_4(v___f_3017_, v___x_3286_, v___y_3019_, v___y_3020_, lean_box(0));
v___y_3207_ = v___x_3270_;
v___y_3208_ = v_a_3215_;
v___y_3209_ = v___x_3287_;
goto v___jp_3206_;
}
else
{
uint8_t v___x_3288_; uint8_t v___x_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; uint64_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec_ref(v___f_3017_);
v___x_3288_ = 1;
v___x_3289_ = 0;
v___x_3290_ = 2;
v___x_3291_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3291_, 0, v___x_3283_);
lean_ctor_set_uint8(v___x_3291_, 1, v___x_3283_);
lean_ctor_set_uint8(v___x_3291_, 2, v___x_3283_);
lean_ctor_set_uint8(v___x_3291_, 3, v___x_3283_);
lean_ctor_set_uint8(v___x_3291_, 4, v___x_3283_);
lean_ctor_set_uint8(v___x_3291_, 5, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 6, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 7, v___x_3283_);
lean_ctor_set_uint8(v___x_3291_, 8, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 9, v___x_3288_);
lean_ctor_set_uint8(v___x_3291_, 10, v___x_3289_);
lean_ctor_set_uint8(v___x_3291_, 11, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 12, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 13, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 14, v___x_3290_);
lean_ctor_set_uint8(v___x_3291_, 15, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 16, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 17, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 18, v___x_3217_);
lean_ctor_set_uint8(v___x_3291_, 19, v___x_3283_);
v___x_3292_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set_uint64(v___x_3293_, sizeof(void*)*1, v___x_3292_);
v___x_3294_ = lean_box(1);
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3297_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3299_, 0, v___x_3293_);
lean_ctor_set(v___x_3299_, 1, v___x_3294_);
lean_ctor_set(v___x_3299_, 2, v___x_3296_);
lean_ctor_set(v___x_3299_, 3, v___x_3297_);
lean_ctor_set(v___x_3299_, 4, v___x_3298_);
lean_ctor_set(v___x_3299_, 5, v___x_3295_);
lean_ctor_set(v___x_3299_, 6, v___x_3298_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*7, v___x_3283_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*7 + 1, v___x_3283_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*7 + 2, v___x_3283_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*7 + 3, v___x_3217_);
v___x_3300_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3301_ = lean_st_mk_ref(v___x_3300_);
v___x_3302_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3275_, v___x_3217_, v___x_3299_, v___x_3301_, v___y_3019_, v___y_3020_);
lean_dec_ref_known(v___x_3299_, 7);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = lean_st_ref_get(v___x_3301_);
lean_dec(v___x_3301_);
lean_dec(v___x_3304_);
v___y_3190_ = v___x_3270_;
v___y_3191_ = v_a_3215_;
v___y_3192_ = v___x_3217_;
v___y_3193_ = v___x_3283_;
v_a_3194_ = v_a_3303_;
goto v___jp_3189_;
}
else
{
lean_dec(v___x_3301_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3305_; 
v_a_3305_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3302_, 1);
v___y_3190_ = v___x_3270_;
v___y_3191_ = v_a_3215_;
v___y_3192_ = v___x_3217_;
v___y_3193_ = v___x_3283_;
v_a_3194_ = v_a_3305_;
goto v___jp_3189_;
}
else
{
lean_object* v_a_3306_; 
v_a_3306_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3302_, 1);
v___y_3202_ = v___x_3270_;
v___y_3203_ = v_a_3215_;
v_a_3204_ = v_a_3306_;
goto v___jp_3201_;
}
}
}
}
else
{
uint8_t v___x_3307_; uint8_t v___x_3308_; uint8_t v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; uint64_t v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
lean_dec(v_snd_3276_);
lean_dec_ref(v___f_3017_);
v___x_3307_ = 0;
v___x_3308_ = 1;
v___x_3309_ = 0;
v___x_3310_ = 2;
v___x_3311_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3311_, 0, v___x_3307_);
lean_ctor_set_uint8(v___x_3311_, 1, v___x_3307_);
lean_ctor_set_uint8(v___x_3311_, 2, v___x_3307_);
lean_ctor_set_uint8(v___x_3311_, 3, v___x_3307_);
lean_ctor_set_uint8(v___x_3311_, 4, v___x_3307_);
lean_ctor_set_uint8(v___x_3311_, 5, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 6, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 7, v___x_3307_);
lean_ctor_set_uint8(v___x_3311_, 8, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 9, v___x_3308_);
lean_ctor_set_uint8(v___x_3311_, 10, v___x_3309_);
lean_ctor_set_uint8(v___x_3311_, 11, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 12, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 13, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 14, v___x_3310_);
lean_ctor_set_uint8(v___x_3311_, 15, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 16, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 17, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 18, v___x_3217_);
lean_ctor_set_uint8(v___x_3311_, 19, v___x_3307_);
v___x_3312_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3311_);
v___x_3313_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set_uint64(v___x_3313_, sizeof(void*)*1, v___x_3312_);
v___x_3314_ = lean_box(1);
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3319_, 0, v___x_3313_);
lean_ctor_set(v___x_3319_, 1, v___x_3314_);
lean_ctor_set(v___x_3319_, 2, v___x_3316_);
lean_ctor_set(v___x_3319_, 3, v___x_3317_);
lean_ctor_set(v___x_3319_, 4, v___x_3318_);
lean_ctor_set(v___x_3319_, 5, v___x_3315_);
lean_ctor_set(v___x_3319_, 6, v___x_3318_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*7, v___x_3307_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*7 + 1, v___x_3307_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*7 + 2, v___x_3307_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*7 + 3, v___x_3217_);
v___x_3320_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3321_ = lean_st_mk_ref(v___x_3320_);
v___x_3322_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3275_, v___x_3319_, v___x_3321_, v___y_3019_, v___y_3020_);
lean_dec_ref_known(v___x_3319_, 7);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3324_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = lean_st_ref_get(v___x_3321_);
lean_dec(v___x_3321_);
lean_dec(v___x_3324_);
v___y_3196_ = v___x_3270_;
v___y_3197_ = v_a_3215_;
v___y_3198_ = v___x_3217_;
v_a_3199_ = v_a_3323_;
goto v___jp_3195_;
}
else
{
lean_dec(v___x_3321_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3325_; 
v_a_3325_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3322_, 1);
v___y_3196_ = v___x_3270_;
v___y_3197_ = v_a_3215_;
v___y_3198_ = v___x_3217_;
v_a_3199_ = v_a_3325_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3326_; 
v_a_3326_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3322_, 1);
v___y_3202_ = v___x_3270_;
v___y_3203_ = v_a_3215_;
v_a_3204_ = v_a_3326_;
goto v___jp_3201_;
}
}
}
}
}
else
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec(v___x_3273_);
lean_dec(v_name_3018_);
v___x_3327_ = lean_box(0);
lean_inc(v___y_3020_);
lean_inc_ref(v___y_3019_);
v___x_3328_ = lean_apply_4(v___f_3017_, v___x_3327_, v___y_3019_, v___y_3020_, lean_box(0));
v___y_3207_ = v___x_3270_;
v___y_3208_ = v_a_3215_;
v___y_3209_ = v___x_3328_;
goto v___jp_3206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___f_3436_, lean_object* v_name_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_3436_, v_name_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
return v_res_3441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3485_ = lean_unsigned_to_nat(3137104340u);
v___x_3486_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3487_ = l_Lean_Name_num___override(v___x_3486_, v___x_3485_);
return v___x_3487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3490_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3491_ = l_Lean_Name_str___override(v___x_3490_, v___x_3489_);
return v___x_3491_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3494_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3495_ = l_Lean_Name_str___override(v___x_3494_, v___x_3493_);
return v___x_3495_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = lean_unsigned_to_nat(2u);
v___x_3497_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3498_ = l_Lean_Name_num___override(v___x_3497_, v___x_3496_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3500_; lean_object* v___x_3501_; 
v___f_3500_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3501_ = l_Lean_registerReservedNameAction(v___f_3500_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v___x_3502_; uint8_t v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
lean_dec_ref_known(v___x_3501_, 1);
v___x_3502_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3503_ = 0;
v___x_3504_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3505_ = l_Lean_registerTraceClass(v___x_3502_, v___x_3503_, v___x_3504_);
return v___x_3505_;
}
else
{
return v___x_3501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3508_, lean_object* v_x_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3509_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3514_, lean_object* v_x_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3514_, v_x_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3519_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_RecExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LetToHave(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
