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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ReservedNameAction"};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 245, 189, 90, 36, 141, 82, 229)}};
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value)} };
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
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_213_ = lean_string_dec_eq(v_s_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
v___x_215_ = lean_string_dec_eq(v_s_211_, v___x_214_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_211_);
return v___x_216_;
}
else
{
lean_dec_ref(v_s_211_);
return v___x_215_;
}
}
else
{
lean_dec_ref(v_s_211_);
return v___x_213_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* v_str_223_, lean_object* v_env_224_, uint8_t v___x_225_, lean_object* v_as_x27_226_, lean_object* v_b_227_){
_start:
{
if (lean_obj_tag(v_as_x27_226_) == 0)
{
lean_dec_ref(v_env_224_);
lean_dec_ref(v_str_223_);
lean_inc_ref(v_b_227_);
return v_b_227_;
}
else
{
lean_object* v_head_228_; lean_object* v_tail_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___y_233_; uint8_t v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_head_228_ = lean_ctor_get(v_as_x27_226_, 0);
v_tail_229_ = lean_ctor_get(v_as_x27_226_, 1);
v___x_230_ = lean_box(0);
v___x_231_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_239_ = 0;
lean_inc_ref(v_env_224_);
v___x_240_ = l_Lean_Environment_setExporting(v_env_224_, v___x_239_);
lean_inc(v_head_228_);
v___x_241_ = l_Lean_Environment_isSafeDefinition(v___x_240_, v_head_228_);
if (v___x_241_ == 0)
{
v___y_233_ = v___x_241_;
goto v___jp_232_;
}
else
{
uint8_t v___x_242_; 
lean_inc(v_head_228_);
lean_inc_ref(v_env_224_);
v___x_242_ = l_Lean_Meta_isMatcherCore(v_env_224_, v_head_228_);
if (v___x_242_ == 0)
{
v___y_233_ = v___x_225_;
goto v___jp_232_;
}
else
{
v_as_x27_226_ = v_tail_229_;
v_b_227_ = v___x_231_;
goto _start;
}
}
v___jp_232_:
{
if (v___y_233_ == 0)
{
v_as_x27_226_ = v_tail_229_;
v_b_227_ = v___x_231_;
goto _start;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v_env_224_);
lean_inc(v_head_228_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_head_228_);
lean_ctor_set(v___x_235_, 1, v_str_223_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_230_);
return v___x_238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* v_str_244_, lean_object* v_env_245_, lean_object* v___x_246_, lean_object* v_as_x27_247_, lean_object* v_b_248_){
_start:
{
uint8_t v___x_616__boxed_249_; lean_object* v_res_250_; 
v___x_616__boxed_249_ = lean_unbox(v___x_246_);
v_res_250_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_244_, v_env_245_, v___x_616__boxed_249_, v_as_x27_247_, v_b_248_);
lean_dec_ref(v_b_248_);
lean_dec(v_as_x27_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* v_env_251_, lean_object* v_name_252_){
_start:
{
if (lean_obj_tag(v_name_252_) == 1)
{
lean_object* v_pre_253_; lean_object* v_str_254_; uint8_t v___x_255_; 
v_pre_253_ = lean_ctor_get(v_name_252_, 0);
lean_inc(v_pre_253_);
v_str_254_ = lean_ctor_get(v_name_252_, 1);
lean_inc_ref_n(v_str_254_, 2);
lean_dec_ref_known(v_name_252_, 2);
v___x_255_ = l_Lean_Meta_isEqnLikeSuffix(v_str_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec_ref(v_str_254_);
lean_dec(v_pre_253_);
lean_dec_ref(v_env_251_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_fst_264_; 
lean_inc(v_pre_253_);
v___x_257_ = l_Lean_privateToUserName(v_pre_253_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v_pre_253_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_box(0);
v___x_262_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0));
v___x_263_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_254_, v_env_251_, v___x_255_, v___x_260_, v___x_262_);
lean_dec_ref_known(v___x_260_, 2);
v_fst_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_fst_264_);
lean_dec_ref(v___x_263_);
if (lean_obj_tag(v_fst_264_) == 0)
{
return v___x_261_;
}
else
{
lean_object* v_val_265_; 
v_val_265_ = lean_ctor_get(v_fst_264_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v_fst_264_, 1);
return v_val_265_;
}
}
}
else
{
lean_object* v___x_266_; 
lean_dec(v_name_252_);
lean_dec_ref(v_env_251_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(lean_object* v_str_267_, lean_object* v_env_268_, uint8_t v___x_269_, lean_object* v_as_270_, lean_object* v_as_x27_271_, lean_object* v_b_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(v_str_267_, v_env_268_, v___x_269_, v_as_x27_271_, v_b_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* v_str_275_, lean_object* v_env_276_, lean_object* v___x_277_, lean_object* v_as_278_, lean_object* v_as_x27_279_, lean_object* v_b_280_, lean_object* v_a_281_){
_start:
{
uint8_t v___x_687__boxed_282_; lean_object* v_res_283_; 
v___x_687__boxed_282_ = lean_unbox(v___x_277_);
v_res_283_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(v_str_275_, v_env_276_, v___x_687__boxed_282_, v_as_278_, v_as_x27_279_, v_b_280_, v_a_281_);
lean_dec_ref(v_b_280_);
lean_dec(v_as_x27_279_);
lean_dec(v_as_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* v_env_284_, lean_object* v_declName_285_, lean_object* v_suffix_286_){
_start:
{
uint8_t v_isExposed_287_; lean_object* v_name_288_; 
lean_inc(v_declName_285_);
lean_inc_ref(v_env_284_);
v_isExposed_287_ = l_Lean_Environment_hasExposedBody(v_env_284_, v_declName_285_);
v_name_288_ = l_Lean_Name_str___override(v_declName_285_, v_suffix_286_);
if (v_isExposed_287_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_mkPrivateName(v_env_284_, v_name_288_);
lean_dec_ref(v_env_284_);
return v___x_289_;
}
else
{
lean_dec_ref(v_env_284_);
return v_name_288_;
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_290_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_ctor_set(v___x_295_, 2, v___x_294_);
lean_ctor_set(v___x_295_, 3, v___x_294_);
lean_ctor_set(v___x_295_, 4, v___x_293_);
lean_ctor_set(v___x_295_, 5, v___x_293_);
lean_ctor_set(v___x_295_, 6, v___x_293_);
lean_ctor_set(v___x_295_, 7, v___x_293_);
lean_ctor_set(v___x_295_, 8, v___x_293_);
lean_ctor_set(v___x_295_, 9, v___x_293_);
lean_ctor_set(v___x_295_, 10, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_unsigned_to_nat(32u);
v___x_297_ = lean_mk_empty_array_with_capacity(v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = ((size_t)5ULL);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_unsigned_to_nat(32u);
v___x_302_ = lean_mk_empty_array_with_capacity(v___x_301_);
v___x_303_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
v___x_304_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_300_);
lean_ctor_set(v___x_304_, 3, v___x_300_);
lean_ctor_set_usize(v___x_304_, 4, v___x_299_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = lean_box(1);
v___x_306_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_307_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
v___x_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
lean_ctor_set(v___x_308_, 2, v___x_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v_toCold_314_; lean_object* v_env_315_; lean_object* v_options_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_313_ = lean_st_ref_get(v___y_311_);
v_toCold_314_ = lean_ctor_get(v___y_310_, 0);
v_env_315_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_env_315_);
lean_dec(v___x_313_);
v_options_316_ = lean_ctor_get(v_toCold_314_, 2);
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_316_);
v___x_319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_319_, 0, v_env_315_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v_options_316_);
v___x_320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_msgData_309_);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_ref_331_; lean_object* v___x_332_; lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
v_ref_331_ = lean_ctor_get(v___y_328_, 2);
v___x_332_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_327_, v___y_328_, v___y_329_);
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_341_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
lean_inc(v_ref_331_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v_ref_331_);
lean_ctor_set(v___x_337_, 1, v_a_333_);
if (v_isShared_336_ == 0)
{
lean_ctor_set_tag(v___x_335_, 1);
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_346_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_349_ = l_Lean_stringToMessageData(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_355_ = l_Lean_stringToMessageData(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_356_, lean_object* v_reservedName_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_361_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_362_ = 0;
v___x_363_ = l_Lean_MessageData_ofConstName(v_declName_356_, v___x_362_);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_361_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = 1;
v___x_368_ = l_Lean_MessageData_ofConstName(v_reservedName_357_, v___x_367_);
v___x_369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_366_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_371_, v___y_358_, v___y_359_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_373_, lean_object* v_reservedName_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_373_, v_reservedName_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_379_, lean_object* v_suffix_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; lean_object* v_env_385_; lean_object* v_reservedName_386_; uint8_t v___x_387_; uint8_t v___x_388_; 
v___x_384_ = lean_st_ref_get(v___y_382_);
v_env_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc_ref(v_env_385_);
lean_dec(v___x_384_);
lean_inc(v_declName_379_);
v_reservedName_386_ = l_Lean_Name_str___override(v_declName_379_, v_suffix_380_);
v___x_387_ = 1;
lean_inc(v_reservedName_386_);
v___x_388_ = l_Lean_Environment_contains(v_env_385_, v_reservedName_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_reservedName_386_);
lean_dec(v_declName_379_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_379_, v_reservedName_386_, v___y_381_, v___y_382_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_392_, lean_object* v_suffix_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_392_, v_suffix_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_398_);
v___x_403_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_398_, v___x_402_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref_known(v___x_403_, 1);
v___x_404_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_398_);
v___x_405_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_398_, v___x_404_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref_known(v___x_405_, 1);
v___x_406_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_407_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_398_, v___x_406_, v_a_399_, v_a_400_);
return v___x_407_;
}
else
{
lean_dec(v_declName_398_);
return v___x_405_;
}
}
else
{
lean_dec(v_declName_398_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_413_, lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_414_, v___y_415_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_419_, lean_object* v_msg_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_419_, v_msg_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_424_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_425_, lean_object* v_n_426_){
_start:
{
lean_object* v___x_427_; 
lean_inc(v_n_426_);
lean_inc_ref(v_env_425_);
v___x_427_ = l_Lean_Meta_declFromEqLikeName(v_env_425_, v_n_426_);
if (lean_obj_tag(v___x_427_) == 1)
{
lean_object* v_val_428_; lean_object* v_fst_429_; lean_object* v_snd_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_val_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___x_427_, 1);
v_fst_429_ = lean_ctor_get(v_val_428_, 0);
lean_inc(v_fst_429_);
v_snd_430_ = lean_ctor_get(v_val_428_, 1);
lean_inc(v_snd_430_);
lean_dec(v_val_428_);
v___x_431_ = l_Lean_Meta_mkEqLikeNameFor(v_env_425_, v_fst_429_, v_snd_430_);
v___x_432_ = lean_name_eq(v_n_426_, v___x_431_);
lean_dec(v___x_431_);
lean_dec(v_n_426_);
return v___x_432_;
}
else
{
uint8_t v___x_433_; 
lean_dec(v___x_427_);
lean_dec(v_n_426_);
lean_dec_ref(v_env_425_);
v___x_433_ = 0;
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_434_, lean_object* v_n_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_434_, v_n_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_440_; lean_object* v___x_441_; 
v___f_440_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_441_ = l_Lean_registerReservedNamePredicate(v___f_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_box(0);
v___x_446_ = lean_st_mk_ref(v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_449_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_452_ = lean_mk_io_user_error(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_453_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_initializing();
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref(v_f_453_);
v___x_456_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_458_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_459_ = lean_st_ref_take(v___x_458_);
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v_f_453_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = lean_st_ref_put(v___x_458_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_registerGetEqnsFn(v_f_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_476_; lean_object* v_env_477_; uint8_t v___x_478_; lean_object* v___x_479_; 
v___x_476_ = lean_st_ref_get(v_a_470_);
v_env_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc_ref(v_env_477_);
lean_dec(v___x_476_);
v___x_478_ = 0;
lean_inc(v_declName_466_);
v___x_479_ = l_Lean_Environment_findAsync_x3f(v_env_477_, v_declName_466_, v___x_478_);
if (lean_obj_tag(v___x_479_) == 1)
{
lean_object* v_val_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_511_; 
v_val_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_511_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_511_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_val_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_511_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v_kind_484_; 
v_kind_484_ = lean_ctor_get_uint8(v_val_480_, sizeof(void*)*3);
if (v_kind_484_ == 0)
{
lean_object* v_sig_485_; lean_object* v___x_486_; lean_object* v_env_487_; uint8_t v___x_488_; 
v_sig_485_ = lean_ctor_get(v_val_480_, 1);
lean_inc_ref(v_sig_485_);
lean_dec(v_val_480_);
v___x_486_ = lean_st_ref_get(v_a_470_);
v_env_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc_ref(v_env_487_);
lean_dec(v___x_486_);
v___x_488_ = l_Lean_Meta_isMatcherCore(v_env_487_, v_declName_466_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v_type_490_; lean_object* v___x_491_; 
lean_del_object(v___x_482_);
v___x_489_ = lean_task_get_own(v_sig_485_);
v_type_490_ = lean_ctor_get(v___x_489_, 2);
lean_inc_ref(v_type_490_);
lean_dec(v___x_489_);
v___x_491_ = l_Lean_Meta_isProp(v_type_490_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_506_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_506_ == 0)
{
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_506_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_506_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
uint8_t v___x_496_; 
v___x_496_ = lean_unbox(v_a_492_);
lean_dec(v_a_492_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_497_ = 1;
v___x_498_ = lean_box(v___x_497_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_498_);
v___x_500_ = v___x_494_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_box(v___x_488_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_502_);
v___x_504_ = v___x_494_;
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
}
else
{
return v___x_491_;
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec_ref(v_sig_485_);
v___x_507_ = lean_box(v___x_478_);
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 0);
lean_ctor_set(v___x_482_, 0, v___x_507_);
v___x_509_ = v___x_482_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
lean_del_object(v___x_482_);
lean_dec(v_val_480_);
lean_dec(v_declName_466_);
goto v___jp_472_;
}
}
}
else
{
lean_dec(v___x_479_);
lean_dec(v_declName_466_);
goto v___jp_472_;
}
v___jp_472_:
{
uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = 0;
v___x_474_ = lean_box(v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_518_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_519_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_527_);
return v_res_529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_530_; lean_object* v___f_531_; 
v___x_530_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_531_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_531_, 0, v___x_530_);
return v___f_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___f_533_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_534_ = lean_box(0);
v___x_535_ = lean_box(1);
v___x_536_ = l_Lean_registerEnvExtension___redArg(v___f_533_, v___x_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_538_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_539_, lean_object* v_opt_540_){
_start:
{
lean_object* v_name_541_; lean_object* v_defValue_542_; lean_object* v_map_543_; lean_object* v___x_544_; 
v_name_541_ = lean_ctor_get(v_opt_540_, 0);
v_defValue_542_ = lean_ctor_get(v_opt_540_, 1);
v_map_543_ = lean_ctor_get(v_opts_539_, 0);
v___x_544_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_543_, v_name_541_);
if (lean_obj_tag(v___x_544_) == 0)
{
uint8_t v___x_545_; 
v___x_545_ = lean_unbox(v_defValue_542_);
return v___x_545_;
}
else
{
lean_object* v_val_546_; 
v_val_546_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_544_, 1);
if (lean_obj_tag(v_val_546_) == 1)
{
uint8_t v_v_547_; 
v_v_547_ = lean_ctor_get_uint8(v_val_546_, 0);
lean_dec_ref_known(v_val_546_, 0);
return v_v_547_;
}
else
{
uint8_t v___x_548_; 
lean_dec(v_val_546_);
v___x_548_ = lean_unbox(v_defValue_542_);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_549_, lean_object* v_opt_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_549_, v_opt_550_);
lean_dec_ref(v_opt_550_);
lean_dec_ref(v_opts_549_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_opts_553_, lean_object* v_opt_554_){
_start:
{
lean_object* v_name_555_; lean_object* v_defValue_556_; lean_object* v_map_557_; lean_object* v___x_558_; 
v_name_555_ = lean_ctor_get(v_opt_554_, 0);
v_defValue_556_ = lean_ctor_get(v_opt_554_, 1);
v_map_557_ = lean_ctor_get(v_opts_553_, 0);
v___x_558_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_557_, v_name_555_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_inc(v_defValue_556_);
return v_defValue_556_;
}
else
{
lean_object* v_val_559_; 
v_val_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v___x_558_, 1);
if (lean_obj_tag(v_val_559_) == 3)
{
lean_object* v_v_560_; 
v_v_560_ = lean_ctor_get(v_val_559_, 0);
lean_inc(v_v_560_);
lean_dec_ref_known(v_val_559_, 1);
return v_v_560_;
}
else
{
lean_dec(v_val_559_);
lean_inc(v_defValue_556_);
return v_defValue_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_opts_561_, lean_object* v_opt_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_561_, v_opt_562_);
lean_dec_ref(v_opt_562_);
lean_dec_ref(v_opts_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_567_, size_t v_sz_568_, size_t v_i_569_, lean_object* v_b_570_){
_start:
{
lean_object* v_a_572_; uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_lt(v_i_569_, v_sz_568_);
if (v___x_576_ == 0)
{
return v_b_570_;
}
else
{
lean_object* v_a_577_; lean_object* v_fst_578_; lean_object* v_snd_579_; lean_object* v_map_580_; uint8_t v_hasTrace_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_594_; 
v_a_577_ = lean_array_uget_borrowed(v_as_567_, v_i_569_);
v_fst_578_ = lean_ctor_get(v_a_577_, 0);
v_snd_579_ = lean_ctor_get(v_a_577_, 1);
v_map_580_ = lean_ctor_get(v_b_570_, 0);
v_hasTrace_581_ = lean_ctor_get_uint8(v_b_570_, sizeof(void*)*1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_b_570_);
if (v_isSharedCheck_594_ == 0)
{
v___x_583_ = v_b_570_;
v_isShared_584_ = v_isSharedCheck_594_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_map_580_);
lean_dec(v_b_570_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_594_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; 
lean_inc(v_snd_579_);
lean_inc(v_fst_578_);
v___x_585_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_578_, v_snd_579_, v_map_580_);
if (v_hasTrace_581_ == 0)
{
lean_object* v___x_586_; uint8_t v___x_587_; lean_object* v___x_589_; 
v___x_586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_587_ = l_Lean_Name_isPrefixOf(v___x_586_, v_fst_578_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_589_ = v___x_583_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_585_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_ctor_set_uint8(v___x_589_, sizeof(void*)*1, v___x_587_);
v_a_572_ = v___x_589_;
goto v___jp_571_;
}
}
else
{
lean_object* v___x_592_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_592_ = v___x_583_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_585_);
lean_ctor_set_uint8(v_reuseFailAlloc_593_, sizeof(void*)*1, v_hasTrace_581_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
v_a_572_ = v___x_592_;
goto v___jp_571_;
}
}
}
}
v___jp_571_:
{
size_t v___x_573_; size_t v___x_574_; 
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_569_, v___x_573_);
v_i_569_ = v___x_574_;
v_b_570_ = v_a_572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_595_, lean_object* v_sz_596_, lean_object* v_i_597_, lean_object* v_b_598_){
_start:
{
size_t v_sz_boxed_599_; size_t v_i_boxed_600_; lean_object* v_res_601_; 
v_sz_boxed_599_ = lean_unbox_usize(v_sz_596_);
lean_dec(v_sz_596_);
v_i_boxed_600_ = lean_unbox_usize(v_i_597_);
lean_dec(v_i_597_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_as_595_, v_sz_boxed_599_, v_i_boxed_600_, v_b_598_);
lean_dec_ref(v_as_595_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_602_, lean_object* v_k_603_, uint8_t v_v_604_){
_start:
{
lean_object* v_map_605_; uint8_t v_hasTrace_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_620_; 
v_map_605_ = lean_ctor_get(v_o_602_, 0);
v_hasTrace_606_ = lean_ctor_get_uint8(v_o_602_, sizeof(void*)*1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_o_602_);
if (v_isSharedCheck_620_ == 0)
{
v___x_608_ = v_o_602_;
v_isShared_609_ = v_isSharedCheck_620_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_map_605_);
lean_dec(v_o_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_620_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_610_, 0, v_v_604_);
lean_inc(v_k_603_);
v___x_611_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_603_, v___x_610_, v_map_605_);
if (v_hasTrace_606_ == 0)
{
lean_object* v___x_612_; uint8_t v___x_613_; lean_object* v___x_615_; 
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_613_ = l_Lean_Name_isPrefixOf(v___x_612_, v_k_603_);
lean_dec(v_k_603_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_615_ = v___x_608_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*1, v___x_613_);
return v___x_615_;
}
}
else
{
lean_object* v___x_618_; 
lean_dec(v_k_603_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_618_ = v___x_608_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_611_);
lean_ctor_set_uint8(v_reuseFailAlloc_619_, sizeof(void*)*1, v_hasTrace_606_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_621_, lean_object* v_k_622_, lean_object* v_v_623_){
_start:
{
uint8_t v_v_boxed_624_; lean_object* v_res_625_; 
v_v_boxed_624_ = lean_unbox(v_v_623_);
v_res_625_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_621_, v_k_622_, v_v_boxed_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_626_, lean_object* v_opt_627_, uint8_t v_val_628_){
_start:
{
lean_object* v_name_629_; lean_object* v___x_630_; 
v_name_629_ = lean_ctor_get(v_opt_627_, 0);
lean_inc(v_name_629_);
lean_dec_ref(v_opt_627_);
v___x_630_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_626_, v_name_629_, v_val_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_631_, lean_object* v_opt_632_, lean_object* v_val_633_){
_start:
{
uint8_t v_val_boxed_634_; lean_object* v_res_635_; 
v_val_boxed_634_ = lean_unbox(v_val_633_);
v_res_635_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_631_, v_opt_632_, v_val_boxed_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v_defValue_642_; uint8_t v___x_643_; lean_object* v___x_644_; size_t v___x_645_; size_t v___x_646_; 
v___x_641_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
v_defValue_642_ = lean_ctor_get(v___x_641_, 1);
v___x_643_ = lean_unbox(v_defValue_642_);
lean_inc(v___x_641_);
v___x_644_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_639_, v___x_641_, v___x_643_);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = lean_usize_add(v_i_637_, v___x_645_);
v_i_637_ = v___x_646_;
v_b_639_ = v___x_644_;
goto _start;
}
else
{
return v_b_639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(lean_object* v_as_648_, lean_object* v_i_649_, lean_object* v_stop_650_, lean_object* v_b_651_){
_start:
{
size_t v_i_boxed_652_; size_t v_stop_boxed_653_; lean_object* v_res_654_; 
v_i_boxed_652_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_stop_boxed_653_ = lean_unbox_usize(v_stop_650_);
lean_dec(v_stop_650_);
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v_as_648_, v_i_boxed_652_, v_stop_boxed_653_, v_b_651_);
lean_dec_ref(v_as_648_);
return v_res_654_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Array_instInhabited(lean_box(0));
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = l_Lean_Meta_eqnAffectingOptions;
v___x_662_ = lean_array_get_size(v___x_661_);
return v___x_662_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_nat_dec_lt(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_667_ = lean_nat_dec_le(v___x_666_, v___x_666_);
return v___x_667_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__7(void){
_start:
{
lean_object* v___x_668_; size_t v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_669_ = lean_usize_of_nat(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_670_, lean_object* v_act_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___y_678_; uint8_t v___y_679_; lean_object* v_fileName_680_; lean_object* v_fileMap_681_; lean_object* v_currNamespace_682_; lean_object* v_openDecls_683_; lean_object* v_initHeartbeats_684_; lean_object* v_maxHeartbeats_685_; lean_object* v_quotContext_686_; lean_object* v_currMacroScope_687_; lean_object* v_cancelTk_x3f_688_; lean_object* v_inheritedTraceOptions_689_; lean_object* v_currRecDepth_690_; lean_object* v_ref_691_; uint8_t v_suppressElabErrors_692_; lean_object* v___y_693_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_env_701_; lean_object* v___x_702_; lean_object* v_toEnvExtension_703_; lean_object* v_toCold_704_; lean_object* v_asyncMode_705_; lean_object* v_currRecDepth_706_; lean_object* v_ref_707_; uint8_t v_suppressElabErrors_708_; lean_object* v_fileName_709_; lean_object* v_fileMap_710_; lean_object* v_options_711_; lean_object* v_currNamespace_712_; lean_object* v_openDecls_713_; lean_object* v_initHeartbeats_714_; lean_object* v_maxHeartbeats_715_; lean_object* v_quotContext_716_; lean_object* v_currMacroScope_717_; lean_object* v_cancelTk_x3f_718_; lean_object* v_inheritedTraceOptions_719_; lean_object* v___y_721_; uint8_t v___y_722_; uint8_t v___y_723_; lean_object* v___y_745_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; 
v___x_699_ = lean_st_ref_get(v_a_675_);
v___x_700_ = lean_st_ref_get(v_a_675_);
v_env_701_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_env_701_);
lean_dec(v___x_699_);
v___x_702_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_703_ = lean_ctor_get(v___x_702_, 0);
v_toCold_704_ = lean_ctor_get(v_a_674_, 0);
v_asyncMode_705_ = lean_ctor_get(v_toEnvExtension_703_, 2);
v_currRecDepth_706_ = lean_ctor_get(v_a_674_, 1);
v_ref_707_ = lean_ctor_get(v_a_674_, 2);
v_suppressElabErrors_708_ = lean_ctor_get_uint8(v_a_674_, sizeof(void*)*3 + 1);
v_fileName_709_ = lean_ctor_get(v_toCold_704_, 0);
v_fileMap_710_ = lean_ctor_get(v_toCold_704_, 1);
v_options_711_ = lean_ctor_get(v_toCold_704_, 2);
v_currNamespace_712_ = lean_ctor_get(v_toCold_704_, 4);
v_openDecls_713_ = lean_ctor_get(v_toCold_704_, 5);
v_initHeartbeats_714_ = lean_ctor_get(v_toCold_704_, 6);
v_maxHeartbeats_715_ = lean_ctor_get(v_toCold_704_, 7);
v_quotContext_716_ = lean_ctor_get(v_toCold_704_, 8);
v_currMacroScope_717_ = lean_ctor_get(v_toCold_704_, 9);
v_cancelTk_x3f_718_ = lean_ctor_get(v_toCold_704_, 10);
v_inheritedTraceOptions_719_ = lean_ctor_get(v_toCold_704_, 11);
v___x_750_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_751_ = 0;
v___x_752_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_750_, v___x_702_, v_env_701_, v_declName_670_, v_asyncMode_705_, v___x_751_);
if (lean_obj_tag(v___x_752_) == 1)
{
lean_object* v_val_753_; lean_object* v___y_755_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_val_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_759_ = l_Lean_Meta_eqnAffectingOptions;
v___x_760_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_760_ == 0)
{
lean_inc_ref(v_options_711_);
v___y_755_ = v_options_711_;
goto v___jp_754_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_761_ == 0)
{
if (v___x_760_ == 0)
{
lean_inc_ref(v_options_711_);
v___y_755_ = v_options_711_;
goto v___jp_754_;
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_711_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_759_, v___x_762_, v___x_763_, v_options_711_);
v___y_755_ = v___x_764_;
goto v___jp_754_;
}
}
else
{
size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_765_ = ((size_t)0ULL);
v___x_766_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_711_);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_759_, v___x_765_, v___x_766_, v_options_711_);
v___y_755_ = v___x_767_;
goto v___jp_754_;
}
}
v___jp_754_:
{
size_t v_sz_756_; size_t v___x_757_; lean_object* v___x_758_; 
v_sz_756_ = lean_array_size(v_val_753_);
v___x_757_ = ((size_t)0ULL);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_753_, v_sz_756_, v___x_757_, v___y_755_);
lean_dec(v_val_753_);
v___y_745_ = v___x_758_;
goto v___jp_744_;
}
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
lean_dec(v___x_752_);
v___x_768_ = l_Lean_Meta_eqnAffectingOptions;
v___x_769_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_769_ == 0)
{
lean_inc_ref(v_options_711_);
v___y_745_ = v_options_711_;
goto v___jp_744_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_770_ == 0)
{
if (v___x_769_ == 0)
{
lean_inc_ref(v_options_711_);
v___y_745_ = v_options_711_;
goto v___jp_744_;
}
else
{
size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_771_ = ((size_t)0ULL);
v___x_772_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_711_);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_768_, v___x_771_, v___x_772_, v_options_711_);
v___y_745_ = v___x_773_;
goto v___jp_744_;
}
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)0ULL);
v___x_775_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_711_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_768_, v___x_774_, v___x_775_, v_options_711_);
v___y_745_ = v___x_776_;
goto v___jp_744_;
}
}
}
v___jp_677_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_694_ = l_Lean_maxRecDepth;
v___x_695_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_678_, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_696_, 0, v_fileName_680_);
lean_ctor_set(v___x_696_, 1, v_fileMap_681_);
lean_ctor_set(v___x_696_, 2, v___y_678_);
lean_ctor_set(v___x_696_, 3, v___x_695_);
lean_ctor_set(v___x_696_, 4, v_currNamespace_682_);
lean_ctor_set(v___x_696_, 5, v_openDecls_683_);
lean_ctor_set(v___x_696_, 6, v_initHeartbeats_684_);
lean_ctor_set(v___x_696_, 7, v_maxHeartbeats_685_);
lean_ctor_set(v___x_696_, 8, v_quotContext_686_);
lean_ctor_set(v___x_696_, 9, v_currMacroScope_687_);
lean_ctor_set(v___x_696_, 10, v_cancelTk_x3f_688_);
lean_ctor_set(v___x_696_, 11, v_inheritedTraceOptions_689_);
lean_inc(v_ref_691_);
lean_inc(v_currRecDepth_690_);
v___x_697_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v_currRecDepth_690_);
lean_ctor_set(v___x_697_, 2, v_ref_691_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*3, v___y_679_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*3 + 1, v_suppressElabErrors_692_);
lean_inc(v___y_693_);
lean_inc(v_a_673_);
lean_inc_ref(v_a_672_);
v___x_698_ = lean_apply_5(v_act_671_, v_a_672_, v_a_673_, v___x_697_, v___y_693_, lean_box(0));
return v___x_698_;
}
v___jp_720_:
{
if (v___y_723_ == 0)
{
lean_object* v___x_724_; lean_object* v_env_725_; lean_object* v_nextMacroScope_726_; lean_object* v_ngen_727_; lean_object* v_auxDeclNGen_728_; lean_object* v_traceState_729_; lean_object* v_messages_730_; lean_object* v_infoState_731_; lean_object* v_snapshotTasks_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_742_; 
v___x_724_ = lean_st_ref_take(v_a_675_);
v_env_725_ = lean_ctor_get(v___x_724_, 0);
v_nextMacroScope_726_ = lean_ctor_get(v___x_724_, 1);
v_ngen_727_ = lean_ctor_get(v___x_724_, 2);
v_auxDeclNGen_728_ = lean_ctor_get(v___x_724_, 3);
v_traceState_729_ = lean_ctor_get(v___x_724_, 4);
v_messages_730_ = lean_ctor_get(v___x_724_, 6);
v_infoState_731_ = lean_ctor_get(v___x_724_, 7);
v_snapshotTasks_732_ = lean_ctor_get(v___x_724_, 8);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_724_, 5);
lean_dec(v_unused_743_);
v___x_734_ = v___x_724_;
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_snapshotTasks_732_);
lean_inc(v_infoState_731_);
lean_inc(v_messages_730_);
lean_inc(v_traceState_729_);
lean_inc(v_auxDeclNGen_728_);
lean_inc(v_ngen_727_);
lean_inc(v_nextMacroScope_726_);
lean_inc(v_env_725_);
lean_dec(v___x_724_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_736_ = l_Lean_Kernel_enableDiag(v_env_725_, v___y_722_);
v___x_737_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 5, v___x_737_);
lean_ctor_set(v___x_734_, 0, v___x_736_);
v___x_739_ = v___x_734_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_nextMacroScope_726_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_ngen_727_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v_auxDeclNGen_728_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_traceState_729_);
lean_ctor_set(v_reuseFailAlloc_741_, 5, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_741_, 6, v_messages_730_);
lean_ctor_set(v_reuseFailAlloc_741_, 7, v_infoState_731_);
lean_ctor_set(v_reuseFailAlloc_741_, 8, v_snapshotTasks_732_);
v___x_739_ = v_reuseFailAlloc_741_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; 
v___x_740_ = lean_st_ref_put(v_a_675_, v___x_739_);
lean_inc_ref(v_inheritedTraceOptions_719_);
lean_inc(v_cancelTk_x3f_718_);
lean_inc(v_currMacroScope_717_);
lean_inc(v_quotContext_716_);
lean_inc(v_maxHeartbeats_715_);
lean_inc(v_initHeartbeats_714_);
lean_inc(v_openDecls_713_);
lean_inc(v_currNamespace_712_);
lean_inc_ref(v_fileMap_710_);
lean_inc_ref(v_fileName_709_);
v___y_678_ = v___y_721_;
v___y_679_ = v___y_722_;
v_fileName_680_ = v_fileName_709_;
v_fileMap_681_ = v_fileMap_710_;
v_currNamespace_682_ = v_currNamespace_712_;
v_openDecls_683_ = v_openDecls_713_;
v_initHeartbeats_684_ = v_initHeartbeats_714_;
v_maxHeartbeats_685_ = v_maxHeartbeats_715_;
v_quotContext_686_ = v_quotContext_716_;
v_currMacroScope_687_ = v_currMacroScope_717_;
v_cancelTk_x3f_688_ = v_cancelTk_x3f_718_;
v_inheritedTraceOptions_689_ = v_inheritedTraceOptions_719_;
v_currRecDepth_690_ = v_currRecDepth_706_;
v_ref_691_ = v_ref_707_;
v_suppressElabErrors_692_ = v_suppressElabErrors_708_;
v___y_693_ = v_a_675_;
goto v___jp_677_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_719_);
lean_inc(v_cancelTk_x3f_718_);
lean_inc(v_currMacroScope_717_);
lean_inc(v_quotContext_716_);
lean_inc(v_maxHeartbeats_715_);
lean_inc(v_initHeartbeats_714_);
lean_inc(v_openDecls_713_);
lean_inc(v_currNamespace_712_);
lean_inc_ref(v_fileMap_710_);
lean_inc_ref(v_fileName_709_);
v___y_678_ = v___y_721_;
v___y_679_ = v___y_722_;
v_fileName_680_ = v_fileName_709_;
v_fileMap_681_ = v_fileMap_710_;
v_currNamespace_682_ = v_currNamespace_712_;
v_openDecls_683_ = v_openDecls_713_;
v_initHeartbeats_684_ = v_initHeartbeats_714_;
v_maxHeartbeats_685_ = v_maxHeartbeats_715_;
v_quotContext_686_ = v_quotContext_716_;
v_currMacroScope_687_ = v_currMacroScope_717_;
v_cancelTk_x3f_688_ = v_cancelTk_x3f_718_;
v_inheritedTraceOptions_689_ = v_inheritedTraceOptions_719_;
v_currRecDepth_690_ = v_currRecDepth_706_;
v_ref_691_ = v_ref_707_;
v_suppressElabErrors_692_ = v_suppressElabErrors_708_;
v___y_693_ = v_a_675_;
goto v___jp_677_;
}
}
v___jp_744_:
{
lean_object* v_env_746_; lean_object* v___x_747_; uint8_t v___x_748_; uint8_t v___x_749_; 
v_env_746_ = lean_ctor_get(v___x_700_, 0);
lean_inc_ref(v_env_746_);
lean_dec(v___x_700_);
v___x_747_ = l_Lean_diagnostics;
v___x_748_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_745_, v___x_747_);
v___x_749_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_746_);
lean_dec_ref(v_env_746_);
if (v___x_748_ == 0)
{
if (v___x_749_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_719_);
lean_inc(v_cancelTk_x3f_718_);
lean_inc(v_currMacroScope_717_);
lean_inc(v_quotContext_716_);
lean_inc(v_maxHeartbeats_715_);
lean_inc(v_initHeartbeats_714_);
lean_inc(v_openDecls_713_);
lean_inc(v_currNamespace_712_);
lean_inc_ref(v_fileMap_710_);
lean_inc_ref(v_fileName_709_);
v___y_678_ = v___y_745_;
v___y_679_ = v___x_748_;
v_fileName_680_ = v_fileName_709_;
v_fileMap_681_ = v_fileMap_710_;
v_currNamespace_682_ = v_currNamespace_712_;
v_openDecls_683_ = v_openDecls_713_;
v_initHeartbeats_684_ = v_initHeartbeats_714_;
v_maxHeartbeats_685_ = v_maxHeartbeats_715_;
v_quotContext_686_ = v_quotContext_716_;
v_currMacroScope_687_ = v_currMacroScope_717_;
v_cancelTk_x3f_688_ = v_cancelTk_x3f_718_;
v_inheritedTraceOptions_689_ = v_inheritedTraceOptions_719_;
v_currRecDepth_690_ = v_currRecDepth_706_;
v_ref_691_ = v_ref_707_;
v_suppressElabErrors_692_ = v_suppressElabErrors_708_;
v___y_693_ = v_a_675_;
goto v___jp_677_;
}
else
{
v___y_721_ = v___y_745_;
v___y_722_ = v___x_748_;
v___y_723_ = v___x_748_;
goto v___jp_720_;
}
}
else
{
v___y_721_ = v___y_745_;
v___y_722_ = v___x_748_;
v___y_723_ = v___x_749_;
goto v___jp_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_777_, lean_object* v_act_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_777_, v_act_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_785_, lean_object* v_declName_786_, lean_object* v_act_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_786_, v_act_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_794_, lean_object* v_declName_795_, lean_object* v_act_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_794_, v_declName_795_, v_act_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v_env_807_; lean_object* v_toConstantVal_808_; lean_object* v_value_809_; lean_object* v_all_810_; uint8_t v___y_812_; lean_object* v_type_820_; uint8_t v___x_821_; 
v___x_806_ = lean_st_ref_get(v___y_804_);
v_env_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_ref_n(v_env_807_, 2);
lean_dec(v___x_806_);
v_toConstantVal_808_ = lean_ctor_get(v_thm_803_, 0);
v_value_809_ = lean_ctor_get(v_thm_803_, 1);
v_all_810_ = lean_ctor_get(v_thm_803_, 2);
v_type_820_ = lean_ctor_get(v_toConstantVal_808_, 2);
v___x_821_ = l_Lean_Environment_hasUnsafe(v_env_807_, v_type_820_);
if (v___x_821_ == 0)
{
uint8_t v___x_822_; 
v___x_822_ = l_Lean_Environment_hasUnsafe(v_env_807_, v_value_809_);
v___y_812_ = v___x_822_;
goto v___jp_811_;
}
else
{
lean_dec_ref(v_env_807_);
v___y_812_ = v___x_821_;
goto v___jp_811_;
}
v___jp_811_:
{
if (v___y_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_813_, 0, v_thm_803_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_inc(v_all_810_);
lean_inc_ref(v_value_809_);
lean_inc_ref(v_toConstantVal_808_);
lean_dec_ref(v_thm_803_);
v___x_815_ = lean_box(0);
v___x_816_ = 0;
v___x_817_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_817_, 0, v_toConstantVal_808_);
lean_ctor_set(v___x_817_, 1, v_value_809_);
lean_ctor_set(v___x_817_, 2, v___x_815_);
lean_ctor_set(v___x_817_, 3, v_all_810_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*4, v___x_816_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_823_, v___y_824_);
lean_dec(v___y_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_827_, v___y_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_841_, lean_object* v_b_842_, lean_object* v_c_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
v___x_849_ = lean_apply_7(v_k_841_, v_b_842_, v_c_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, lean_box(0));
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_850_, lean_object* v_b_851_, lean_object* v_c_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_850_, v_b_851_, v_c_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_859_, lean_object* v_k_860_, uint8_t v_cleanupAnnotations_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___f_867_; uint8_t v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_867_, 0, v_k_860_);
v___x_868_ = 1;
v___x_869_ = 0;
v___x_870_ = lean_box(0);
v___x_871_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_859_, v___x_868_, v___x_869_, v___x_868_, v___x_869_, v___x_870_, v___f_867_, v_cleanupAnnotations_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_871_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_871_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_888_, lean_object* v_k_889_, lean_object* v_cleanupAnnotations_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_896_; lean_object* v_res_897_; 
v_cleanupAnnotations_boxed_896_ = lean_unbox(v_cleanupAnnotations_890_);
v_res_897_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_888_, v_k_889_, v_cleanupAnnotations_boxed_896_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_898_, lean_object* v_e_899_, lean_object* v_k_900_, uint8_t v_cleanupAnnotations_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_899_, v_k_900_, v_cleanupAnnotations_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_908_, lean_object* v_e_909_, lean_object* v_k_910_, lean_object* v_cleanupAnnotations_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_917_; lean_object* v_res_918_; 
v_cleanupAnnotations_boxed_917_ = lean_unbox(v_cleanupAnnotations_911_);
v_res_918_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_908_, v_e_909_, v_k_910_, v_cleanupAnnotations_boxed_917_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
if (lean_obj_tag(v_a_919_) == 0)
{
lean_object* v___x_921_; 
v___x_921_ = l_List_reverse___redArg(v_a_920_);
return v___x_921_;
}
else
{
lean_object* v_head_922_; lean_object* v_tail_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_932_; 
v_head_922_ = lean_ctor_get(v_a_919_, 0);
v_tail_923_ = lean_ctor_get(v_a_919_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_932_ == 0)
{
v___x_925_ = v_a_919_;
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_tail_923_);
lean_inc(v_head_922_);
lean_dec(v_a_919_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = l_Lean_mkLevelParam(v_head_922_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v_a_920_);
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_a_920_);
v___x_929_ = v_reuseFailAlloc_931_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v_a_919_ = v_tail_923_;
v_a_920_ = v___x_929_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_933_, lean_object* v_name_934_, lean_object* v_xs_935_, lean_object* v_body_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_name_942_; lean_object* v_levelParams_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_1013_; 
v_name_942_ = lean_ctor_get(v_toConstantVal_933_, 0);
v_levelParams_943_ = lean_ctor_get(v_toConstantVal_933_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_toConstantVal_933_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v_toConstantVal_933_, 2);
lean_dec(v_unused_1014_);
v___x_945_ = v_toConstantVal_933_;
v_isShared_946_ = v_isSharedCheck_1013_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_levelParams_943_);
lean_inc(v_name_942_);
lean_dec(v_toConstantVal_933_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_1013_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_lhs_950_; lean_object* v___x_951_; 
v___x_947_ = lean_box(0);
lean_inc(v_levelParams_943_);
v___x_948_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_943_, v___x_947_);
v___x_949_ = l_Lean_mkConst(v_name_942_, v___x_948_);
v_lhs_950_ = l_Lean_mkAppN(v___x_949_, v_xs_935_);
lean_inc_ref(v_lhs_950_);
v___x_951_ = l_Lean_Meta_mkEq(v_lhs_950_, v_body_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; uint8_t v___x_953_; uint8_t v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = 0;
v___x_954_ = 1;
v___x_955_ = 1;
v___x_956_ = l_Lean_Meta_mkForallFVars(v_xs_935_, v_a_952_, v___x_953_, v___x_954_, v___x_954_, v___x_955_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_958_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = l_Lean_Meta_letToHave(v_a_957_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = l_Lean_Meta_mkEqRefl(v_lhs_950_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = l_Lean_Meta_mkLambdaFVars(v_xs_935_, v_a_961_, v___x_953_, v___x_954_, v___x_953_, v___x_954_, v___x_955_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
lean_inc(v_name_934_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 2, v_a_959_);
lean_ctor_set(v___x_945_, 0, v_name_934_);
v___x_965_ = v___x_945_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_name_934_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_levelParams_943_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_a_959_);
v___x_965_ = v_reuseFailAlloc_972_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v___x_970_; 
lean_inc(v_name_934_);
v___x_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_966_, 0, v_name_934_);
lean_ctor_set(v___x_966_, 1, v___x_947_);
v___x_967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v_a_963_);
lean_ctor_set(v___x_967_, 2, v___x_966_);
v___x_968_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_967_, v___y_940_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
v___x_970_ = l_Lean_addDecl(v_a_969_, v___x_953_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; 
lean_dec_ref_known(v___x_970_, 1);
v___x_971_ = l_Lean_inferDefEqAttr(v_name_934_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_971_;
}
else
{
lean_dec(v_name_934_);
return v___x_970_;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_a_959_);
lean_del_object(v___x_945_);
lean_dec(v_levelParams_943_);
lean_dec(v_name_934_);
v_a_973_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_962_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_962_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_a_959_);
lean_del_object(v___x_945_);
lean_dec(v_levelParams_943_);
lean_dec(v_name_934_);
v_a_981_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_960_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_960_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v_lhs_950_);
lean_del_object(v___x_945_);
lean_dec(v_levelParams_943_);
lean_dec(v_name_934_);
v_a_989_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_958_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_958_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref(v_lhs_950_);
lean_del_object(v___x_945_);
lean_dec(v_levelParams_943_);
lean_dec(v_name_934_);
v_a_997_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_956_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_956_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_lhs_950_);
lean_del_object(v___x_945_);
lean_dec(v_levelParams_943_);
lean_dec(v_name_934_);
v_a_1005_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_951_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_951_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1015_, lean_object* v_name_1016_, lean_object* v_xs_1017_, lean_object* v_body_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1015_, v_name_1016_, v_xs_1017_, v_body_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_xs_1017_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1025_, lean_object* v_info_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_toConstantVal_1032_; lean_object* v_value_1033_; lean_object* v___f_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; 
v_toConstantVal_1032_ = lean_ctor_get(v_info_1026_, 0);
lean_inc_ref(v_toConstantVal_1032_);
v_value_1033_ = lean_ctor_get(v_info_1026_, 1);
lean_inc_ref(v_value_1033_);
lean_dec_ref(v_info_1026_);
v___f_1034_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1034_, 0, v_toConstantVal_1032_);
lean_closure_set(v___f_1034_, 1, v_name_1025_);
v___x_1035_ = 1;
v___x_1036_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1033_, v___f_1034_, v___x_1035_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1037_, lean_object* v_info_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1037_, v_info_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1045_, lean_object* v_name_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1055_; lean_object* v_env_1056_; uint8_t v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_st_ref_get(v_a_1050_);
v_env_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_env_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = 0;
lean_inc(v_declName_1045_);
v___x_1058_ = l_Lean_Environment_find_x3f(v_env_1056_, v_declName_1045_, v___x_1057_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1086_; 
v_val_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1086_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1086_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
if (lean_obj_tag(v_val_1059_) == 1)
{
lean_object* v_val_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_val_1063_ = lean_ctor_get(v_val_1059_, 0);
lean_inc_ref(v_val_1063_);
lean_dec_ref_known(v_val_1059_, 1);
lean_inc_n(v_name_1046_, 2);
v___x_1064_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1064_, 0, v_name_1046_);
lean_closure_set(v___x_1064_, 1, v_val_1063_);
lean_inc(v_declName_1045_);
v___x_1065_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1065_, 0, lean_box(0));
lean_closure_set(v___x_1065_, 1, v_declName_1045_);
lean_closure_set(v___x_1065_, 2, v___x_1064_);
v___x_1066_ = l_Lean_Meta_realizeConst(v_declName_1045_, v_name_1046_, v___x_1065_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1076_; 
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v___x_1066_, 0);
lean_dec(v_unused_1077_);
v___x_1068_ = v___x_1066_;
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
else
{
lean_dec(v___x_1066_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_name_1046_);
v___x_1071_ = v___x_1061_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_name_1046_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1071_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_del_object(v___x_1061_);
lean_dec(v_name_1046_);
v_a_1078_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1066_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1066_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_del_object(v___x_1061_);
lean_dec(v_val_1059_);
lean_dec(v_name_1046_);
lean_dec(v_declName_1045_);
goto v___jp_1052_;
}
}
}
else
{
lean_dec(v___x_1058_);
lean_dec(v_name_1046_);
lean_dec(v_declName_1045_);
goto v___jp_1052_;
}
v___jp_1052_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1087_, lean_object* v_name_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1087_, v_name_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1095_, lean_object* v_vals_1096_, lean_object* v_i_1097_, lean_object* v_k_1098_){
_start:
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_array_get_size(v_keys_1095_);
v___x_1100_ = lean_nat_dec_lt(v_i_1097_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_dec(v_i_1097_);
v___x_1101_ = lean_box(0);
return v___x_1101_;
}
else
{
lean_object* v_k_x27_1102_; uint8_t v___x_1103_; 
v_k_x27_1102_ = lean_array_fget_borrowed(v_keys_1095_, v_i_1097_);
v___x_1103_ = lean_name_eq(v_k_1098_, v_k_x27_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_i_1097_, v___x_1104_);
lean_dec(v_i_1097_);
v_i_1097_ = v___x_1105_;
goto _start;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_array_fget_borrowed(v_vals_1096_, v_i_1097_);
lean_dec(v_i_1097_);
lean_inc(v___x_1107_);
v___x_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1109_, lean_object* v_vals_1110_, lean_object* v_i_1111_, lean_object* v_k_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1109_, v_vals_1110_, v_i_1111_, v_k_1112_);
lean_dec(v_k_1112_);
lean_dec_ref(v_vals_1110_);
lean_dec_ref(v_keys_1109_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1114_, size_t v_x_1115_, lean_object* v_x_1116_){
_start:
{
if (lean_obj_tag(v_x_1114_) == 0)
{
lean_object* v_es_1117_; lean_object* v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; lean_object* v_j_1121_; lean_object* v___x_1122_; 
v_es_1117_ = lean_ctor_get(v_x_1114_, 0);
v___x_1118_ = lean_box(2);
v___x_1119_ = ((size_t)31ULL);
v___x_1120_ = lean_usize_land(v_x_1115_, v___x_1119_);
v_j_1121_ = lean_usize_to_nat(v___x_1120_);
v___x_1122_ = lean_array_get_borrowed(v___x_1118_, v_es_1117_, v_j_1121_);
lean_dec(v_j_1121_);
switch(lean_obj_tag(v___x_1122_))
{
case 0:
{
lean_object* v_key_1123_; lean_object* v_val_1124_; uint8_t v___x_1125_; 
v_key_1123_ = lean_ctor_get(v___x_1122_, 0);
v_val_1124_ = lean_ctor_get(v___x_1122_, 1);
v___x_1125_ = lean_name_eq(v_x_1116_, v_key_1123_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_box(0);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; 
lean_inc(v_val_1124_);
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_val_1124_);
return v___x_1127_;
}
}
case 1:
{
lean_object* v_node_1128_; size_t v___x_1129_; size_t v___x_1130_; 
v_node_1128_ = lean_ctor_get(v___x_1122_, 0);
v___x_1129_ = ((size_t)5ULL);
v___x_1130_ = lean_usize_shift_right(v_x_1115_, v___x_1129_);
v_x_1114_ = v_node_1128_;
v_x_1115_ = v___x_1130_;
goto _start;
}
default: 
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_box(0);
return v___x_1132_;
}
}
}
else
{
lean_object* v_ks_1133_; lean_object* v_vs_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_ks_1133_ = lean_ctor_get(v_x_1114_, 0);
v_vs_1134_ = lean_ctor_get(v_x_1114_, 1);
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1133_, v_vs_1134_, v___x_1135_, v_x_1116_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
size_t v_x_340__boxed_1140_; lean_object* v_res_1141_; 
v_x_340__boxed_1140_ = lean_unbox_usize(v_x_1138_);
lean_dec(v_x_1138_);
v_res_1141_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1137_, v_x_340__boxed_1140_, v_x_1139_);
lean_dec(v_x_1139_);
lean_dec_ref(v_x_1137_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
uint64_t v___y_1145_; 
if (lean_obj_tag(v_x_1143_) == 0)
{
uint64_t v___x_1148_; 
v___x_1148_ = 1723ULL;
v___y_1145_ = v___x_1148_;
goto v___jp_1144_;
}
else
{
uint64_t v_hash_1149_; 
v_hash_1149_ = lean_ctor_get_uint64(v_x_1143_, sizeof(void*)*2);
v___y_1145_ = v_hash_1149_;
goto v___jp_1144_;
}
v___jp_1144_:
{
size_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_uint64_to_usize(v___y_1145_);
v___x_1147_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1142_, v___x_1146_, v_x_1143_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1150_, v_x_1151_);
lean_dec(v_x_1151_);
lean_dec_ref(v_x_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v_env_1157_; lean_object* v___x_1158_; lean_object* v_asyncMode_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1156_ = lean_st_ref_get(v_a_1154_);
v_env_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc_ref(v_env_1157_);
lean_dec(v___x_1156_);
v___x_1158_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1159_ = lean_ctor_get(v___x_1158_, 2);
v___x_1160_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1161_ = lean_box(0);
v___x_1162_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1160_, v___x_1158_, v_env_1157_, v_asyncMode_1159_, v___x_1161_);
v___x_1163_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1162_, v_thmName_1153_);
lean_dec(v___x_1162_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec(v_thmName_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1169_, v_a_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1174_, v_a_1175_, v_a_1176_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_thmName_1174_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1179_, lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1180_, v_x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1183_, v_x_1184_, v_x_1185_);
lean_dec(v_x_1185_);
lean_dec_ref(v_x_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1187_, lean_object* v_x_1188_, size_t v_x_1189_, lean_object* v_x_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1188_, v_x_1189_, v_x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_){
_start:
{
size_t v_x_433__boxed_1196_; lean_object* v_res_1197_; 
v_x_433__boxed_1196_ = lean_unbox_usize(v_x_1194_);
lean_dec(v_x_1194_);
v_res_1197_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1192_, v_x_1193_, v_x_433__boxed_1196_, v_x_1195_);
lean_dec(v_x_1195_);
lean_dec_ref(v_x_1193_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1198_, lean_object* v_keys_1199_, lean_object* v_vals_1200_, lean_object* v_heq_1201_, lean_object* v_i_1202_, lean_object* v_k_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1199_, v_vals_1200_, v_i_1202_, v_k_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1205_, lean_object* v_keys_1206_, lean_object* v_vals_1207_, lean_object* v_heq_1208_, lean_object* v_i_1209_, lean_object* v_k_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1205_, v_keys_1206_, v_vals_1207_, v_heq_1208_, v_i_1209_, v_k_1210_);
lean_dec(v_k_1210_);
lean_dec_ref(v_vals_1207_);
lean_dec_ref(v_keys_1206_);
return v_res_1211_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1212_, lean_object* v_i_1213_, lean_object* v_k_1214_){
_start:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_array_get_size(v_keys_1212_);
v___x_1216_ = lean_nat_dec_lt(v_i_1213_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec(v_i_1213_);
return v___x_1216_;
}
else
{
lean_object* v_k_x27_1217_; uint8_t v___x_1218_; 
v_k_x27_1217_ = lean_array_fget_borrowed(v_keys_1212_, v_i_1213_);
v___x_1218_ = lean_name_eq(v_k_1214_, v_k_x27_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_nat_add(v_i_1213_, v___x_1219_);
lean_dec(v_i_1213_);
v_i_1213_ = v___x_1220_;
goto _start;
}
else
{
lean_dec(v_i_1213_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1222_, lean_object* v_i_1223_, lean_object* v_k_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1222_, v_i_1223_, v_k_1224_);
lean_dec(v_k_1224_);
lean_dec_ref(v_keys_1222_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1227_, size_t v_x_1228_, lean_object* v_x_1229_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 0)
{
lean_object* v_es_1230_; lean_object* v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; lean_object* v_j_1234_; lean_object* v___x_1235_; 
v_es_1230_ = lean_ctor_get(v_x_1227_, 0);
v___x_1231_ = lean_box(2);
v___x_1232_ = ((size_t)31ULL);
v___x_1233_ = lean_usize_land(v_x_1228_, v___x_1232_);
v_j_1234_ = lean_usize_to_nat(v___x_1233_);
v___x_1235_ = lean_array_get_borrowed(v___x_1231_, v_es_1230_, v_j_1234_);
lean_dec(v_j_1234_);
switch(lean_obj_tag(v___x_1235_))
{
case 0:
{
lean_object* v_key_1236_; uint8_t v___x_1237_; 
v_key_1236_ = lean_ctor_get(v___x_1235_, 0);
v___x_1237_ = lean_name_eq(v_x_1229_, v_key_1236_);
return v___x_1237_;
}
case 1:
{
lean_object* v_node_1238_; size_t v___x_1239_; size_t v___x_1240_; 
v_node_1238_ = lean_ctor_get(v___x_1235_, 0);
v___x_1239_ = ((size_t)5ULL);
v___x_1240_ = lean_usize_shift_right(v_x_1228_, v___x_1239_);
v_x_1227_ = v_node_1238_;
v_x_1228_ = v___x_1240_;
goto _start;
}
default: 
{
uint8_t v___x_1242_; 
v___x_1242_ = 0;
return v___x_1242_;
}
}
}
else
{
lean_object* v_ks_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_ks_1243_ = lean_ctor_get(v_x_1227_, 0);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1243_, v___x_1244_, v_x_1229_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
size_t v_x_324__boxed_1249_; uint8_t v_res_1250_; lean_object* v_r_1251_; 
v_x_324__boxed_1249_ = lean_unbox_usize(v_x_1247_);
lean_dec(v_x_1247_);
v_res_1250_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1246_, v_x_324__boxed_1249_, v_x_1248_);
lean_dec(v_x_1248_);
lean_dec_ref(v_x_1246_);
v_r_1251_ = lean_box(v_res_1250_);
return v_r_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
uint64_t v___y_1255_; 
if (lean_obj_tag(v_x_1253_) == 0)
{
uint64_t v___x_1258_; 
v___x_1258_ = 1723ULL;
v___y_1255_ = v___x_1258_;
goto v___jp_1254_;
}
else
{
uint64_t v_hash_1259_; 
v_hash_1259_ = lean_ctor_get_uint64(v_x_1253_, sizeof(void*)*2);
v___y_1255_ = v_hash_1259_;
goto v___jp_1254_;
}
v___jp_1254_:
{
size_t v___x_1256_; uint8_t v___x_1257_; 
v___x_1256_ = lean_uint64_to_usize(v___y_1255_);
v___x_1257_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1252_, v___x_1256_, v_x_1253_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_res_1262_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1260_, v_x_1261_);
lean_dec(v_x_1261_);
lean_dec_ref(v_x_1260_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v___x_1267_; lean_object* v_env_1268_; lean_object* v___x_1269_; lean_object* v_asyncMode_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1267_ = lean_st_ref_get(v_a_1265_);
v_env_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc_ref(v_env_1268_);
lean_dec(v___x_1267_);
v___x_1269_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1270_ = lean_ctor_get(v___x_1269_, 2);
v___x_1271_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1272_ = lean_box(0);
v___x_1273_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1271_, v___x_1269_, v_env_1268_, v_asyncMode_1270_, v___x_1272_);
v___x_1274_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1273_, v_thmName_1264_);
lean_dec(v___x_1273_);
v___x_1275_ = lean_box(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1277_, v_a_1278_);
lean_dec(v_a_1278_);
lean_dec(v_thmName_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1281_, v_a_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_isEqnThm(v_thmName_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_thmName_1286_);
return v_res_1290_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1292_, v_x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
uint8_t v_res_1298_; lean_object* v_r_1299_; 
v_res_1298_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1295_, v_x_1296_, v_x_1297_);
lean_dec(v_x_1297_);
lean_dec_ref(v_x_1296_);
v_r_1299_ = lean_box(v_res_1298_);
return v_r_1299_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1300_, lean_object* v_x_1301_, size_t v_x_1302_, lean_object* v_x_1303_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1301_, v_x_1302_, v_x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
size_t v_x_413__boxed_1309_; uint8_t v_res_1310_; lean_object* v_r_1311_; 
v_x_413__boxed_1309_ = lean_unbox_usize(v_x_1307_);
lean_dec(v_x_1307_);
v_res_1310_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1305_, v_x_1306_, v_x_413__boxed_1309_, v_x_1308_);
lean_dec(v_x_1308_);
lean_dec_ref(v_x_1306_);
v_r_1311_ = lean_box(v_res_1310_);
return v_r_1311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1312_, lean_object* v_keys_1313_, lean_object* v_vals_1314_, lean_object* v_heq_1315_, lean_object* v_i_1316_, lean_object* v_k_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1313_, v_i_1316_, v_k_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1319_, lean_object* v_keys_1320_, lean_object* v_vals_1321_, lean_object* v_heq_1322_, lean_object* v_i_1323_, lean_object* v_k_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1319_, v_keys_1320_, v_vals_1321_, v_heq_1322_, v_i_1323_, v_k_1324_);
lean_dec(v_k_1324_);
lean_dec_ref(v_vals_1321_);
lean_dec_ref(v_keys_1320_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v_ks_1331_; lean_object* v_vs_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1356_; 
v_ks_1331_ = lean_ctor_get(v_x_1327_, 0);
v_vs_1332_ = lean_ctor_get(v_x_1327_, 1);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_x_1327_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1334_ = v_x_1327_;
v_isShared_1335_ = v_isSharedCheck_1356_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_vs_1332_);
lean_inc(v_ks_1331_);
lean_dec(v_x_1327_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1356_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_array_get_size(v_ks_1331_);
v___x_1337_ = lean_nat_dec_lt(v_x_1328_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_dec(v_x_1328_);
v___x_1338_ = lean_array_push(v_ks_1331_, v_x_1329_);
v___x_1339_ = lean_array_push(v_vs_1332_, v_x_1330_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1339_);
lean_ctor_set(v___x_1334_, 0, v___x_1338_);
v___x_1341_ = v___x_1334_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
else
{
lean_object* v_k_x27_1343_; uint8_t v___x_1344_; 
v_k_x27_1343_ = lean_array_fget_borrowed(v_ks_1331_, v_x_1328_);
v___x_1344_ = lean_name_eq(v_x_1329_, v_k_x27_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1346_; 
if (v_isShared_1335_ == 0)
{
v___x_1346_ = v___x_1334_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_ks_1331_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_vs_1332_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_nat_add(v_x_1328_, v___x_1347_);
lean_dec(v_x_1328_);
v_x_1327_ = v___x_1346_;
v_x_1328_ = v___x_1348_;
goto _start;
}
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_array_fset(v_ks_1331_, v_x_1328_, v_x_1329_);
v___x_1352_ = lean_array_fset(v_vs_1332_, v_x_1328_, v_x_1330_);
lean_dec(v_x_1328_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1352_);
lean_ctor_set(v___x_1334_, 0, v___x_1351_);
v___x_1354_ = v___x_1334_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1357_, lean_object* v_k_1358_, lean_object* v_v_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1357_, v___x_1360_, v_k_1358_, v_v_1359_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1363_, size_t v_x_1364_, size_t v_x_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 0)
{
lean_object* v_es_1368_; size_t v___x_1369_; size_t v___x_1370_; lean_object* v_j_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_es_1368_ = lean_ctor_get(v_x_1363_, 0);
v___x_1369_ = ((size_t)31ULL);
v___x_1370_ = lean_usize_land(v_x_1364_, v___x_1369_);
v_j_1371_ = lean_usize_to_nat(v___x_1370_);
v___x_1372_ = lean_array_get_size(v_es_1368_);
v___x_1373_ = lean_nat_dec_lt(v_j_1371_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_dec(v_j_1371_);
lean_dec(v_x_1367_);
lean_dec(v_x_1366_);
return v_x_1363_;
}
else
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1412_; 
lean_inc_ref(v_es_1368_);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_x_1363_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_x_1363_, 0);
lean_dec(v_unused_1413_);
v___x_1375_ = v_x_1363_;
v_isShared_1376_ = v_isSharedCheck_1412_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v_x_1363_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1412_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_v_1377_; lean_object* v___x_1378_; lean_object* v_xs_x27_1379_; lean_object* v___y_1381_; 
v_v_1377_ = lean_array_fget(v_es_1368_, v_j_1371_);
v___x_1378_ = lean_box(0);
v_xs_x27_1379_ = lean_array_fset(v_es_1368_, v_j_1371_, v___x_1378_);
switch(lean_obj_tag(v_v_1377_))
{
case 0:
{
lean_object* v_key_1386_; lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v_key_1386_ = lean_ctor_get(v_v_1377_, 0);
v_val_1387_ = lean_ctor_get(v_v_1377_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_v_1377_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1389_ = v_v_1377_;
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_inc(v_key_1386_);
lean_dec(v_v_1377_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_name_eq(v_x_1366_, v_key_1386_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_del_object(v___x_1389_);
v___x_1392_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1386_, v_val_1387_, v_x_1366_, v_x_1367_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
v___y_1381_ = v___x_1393_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1395_; 
lean_dec(v_val_1387_);
lean_dec(v_key_1386_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v_x_1367_);
lean_ctor_set(v___x_1389_, 0, v_x_1366_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_x_1366_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_x_1367_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
v___y_1381_ = v___x_1395_;
goto v___jp_1380_;
}
}
}
}
case 1:
{
lean_object* v_node_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1410_; 
v_node_1398_ = lean_ctor_get(v_v_1377_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_v_1377_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1400_ = v_v_1377_;
v_isShared_1401_ = v_isSharedCheck_1410_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_node_1398_);
lean_dec(v_v_1377_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1410_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
size_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1402_ = ((size_t)5ULL);
v___x_1403_ = lean_usize_shift_right(v_x_1364_, v___x_1402_);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = lean_usize_add(v_x_1365_, v___x_1404_);
v___x_1406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1398_, v___x_1403_, v___x_1405_, v_x_1366_, v_x_1367_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1406_);
v___x_1408_ = v___x_1400_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
v___y_1381_ = v___x_1408_;
goto v___jp_1380_;
}
}
}
default: 
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_x_1366_);
lean_ctor_set(v___x_1411_, 1, v_x_1367_);
v___y_1381_ = v___x_1411_;
goto v___jp_1380_;
}
}
v___jp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_array_fset(v_xs_x27_1379_, v_j_1371_, v___y_1381_);
lean_dec(v_j_1371_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1382_);
v___x_1384_ = v___x_1375_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
else
{
lean_object* v_ks_1414_; lean_object* v_vs_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1433_; 
v_ks_1414_ = lean_ctor_get(v_x_1363_, 0);
v_vs_1415_ = lean_ctor_get(v_x_1363_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1363_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1417_ = v_x_1363_;
v_isShared_1418_ = v_isSharedCheck_1433_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_vs_1415_);
lean_inc(v_ks_1414_);
lean_dec(v_x_1363_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1433_;
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
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_ks_1414_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_vs_1415_);
v___x_1420_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v_newNode_1421_; size_t v___x_1422_; uint8_t v___x_1423_; 
v_newNode_1421_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1420_, v_x_1366_, v_x_1367_);
v___x_1422_ = ((size_t)7ULL);
v___x_1423_ = lean_usize_dec_le(v___x_1422_, v_x_1365_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1424_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1421_);
v___x_1425_ = lean_unsigned_to_nat(4u);
v___x_1426_ = lean_nat_dec_lt(v___x_1424_, v___x_1425_);
lean_dec(v___x_1424_);
if (v___x_1426_ == 0)
{
lean_object* v_ks_1427_; lean_object* v_vs_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_ks_1427_ = lean_ctor_get(v_newNode_1421_, 0);
lean_inc_ref(v_ks_1427_);
v_vs_1428_ = lean_ctor_get(v_newNode_1421_, 1);
lean_inc_ref(v_vs_1428_);
lean_dec_ref(v_newNode_1421_);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1431_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1365_, v_ks_1427_, v_vs_1428_, v___x_1429_, v___x_1430_);
lean_dec_ref(v_vs_1428_);
lean_dec_ref(v_ks_1427_);
return v___x_1431_;
}
else
{
return v_newNode_1421_;
}
}
else
{
return v_newNode_1421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1434_, lean_object* v_keys_1435_, lean_object* v_vals_1436_, lean_object* v_i_1437_, lean_object* v_entries_1438_){
_start:
{
lean_object* v___x_1439_; uint8_t v___x_1440_; 
v___x_1439_ = lean_array_get_size(v_keys_1435_);
v___x_1440_ = lean_nat_dec_lt(v_i_1437_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_dec(v_i_1437_);
return v_entries_1438_;
}
else
{
lean_object* v_k_1441_; lean_object* v_v_1442_; uint64_t v___y_1444_; 
v_k_1441_ = lean_array_fget_borrowed(v_keys_1435_, v_i_1437_);
v_v_1442_ = lean_array_fget_borrowed(v_vals_1436_, v_i_1437_);
if (lean_obj_tag(v_k_1441_) == 0)
{
uint64_t v___x_1455_; 
v___x_1455_ = 1723ULL;
v___y_1444_ = v___x_1455_;
goto v___jp_1443_;
}
else
{
uint64_t v_hash_1456_; 
v_hash_1456_ = lean_ctor_get_uint64(v_k_1441_, sizeof(void*)*2);
v___y_1444_ = v_hash_1456_;
goto v___jp_1443_;
}
v___jp_1443_:
{
size_t v_h_1445_; size_t v___x_1446_; lean_object* v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; size_t v___x_1450_; size_t v_h_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_h_1445_ = lean_uint64_to_usize(v___y_1444_);
v___x_1446_ = ((size_t)5ULL);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = ((size_t)1ULL);
v___x_1449_ = lean_usize_sub(v_depth_1434_, v___x_1448_);
v___x_1450_ = lean_usize_mul(v___x_1446_, v___x_1449_);
v_h_1451_ = lean_usize_shift_right(v_h_1445_, v___x_1450_);
v___x_1452_ = lean_nat_add(v_i_1437_, v___x_1447_);
lean_dec(v_i_1437_);
lean_inc(v_v_1442_);
lean_inc(v_k_1441_);
v___x_1453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1438_, v_h_1451_, v_depth_1434_, v_k_1441_, v_v_1442_);
v_i_1437_ = v___x_1452_;
v_entries_1438_ = v___x_1453_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1457_, lean_object* v_keys_1458_, lean_object* v_vals_1459_, lean_object* v_i_1460_, lean_object* v_entries_1461_){
_start:
{
size_t v_depth_boxed_1462_; lean_object* v_res_1463_; 
v_depth_boxed_1462_ = lean_unbox_usize(v_depth_1457_);
lean_dec(v_depth_1457_);
v_res_1463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1462_, v_keys_1458_, v_vals_1459_, v_i_1460_, v_entries_1461_);
lean_dec_ref(v_vals_1459_);
lean_dec_ref(v_keys_1458_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
size_t v_x_625__boxed_1469_; size_t v_x_626__boxed_1470_; lean_object* v_res_1471_; 
v_x_625__boxed_1469_ = lean_unbox_usize(v_x_1465_);
lean_dec(v_x_1465_);
v_x_626__boxed_1470_ = lean_unbox_usize(v_x_1466_);
lean_dec(v_x_1466_);
v_res_1471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1464_, v_x_625__boxed_1469_, v_x_626__boxed_1470_, v_x_1467_, v_x_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
uint64_t v___y_1476_; 
if (lean_obj_tag(v_x_1473_) == 0)
{
uint64_t v___x_1480_; 
v___x_1480_ = 1723ULL;
v___y_1476_ = v___x_1480_;
goto v___jp_1475_;
}
else
{
uint64_t v_hash_1481_; 
v_hash_1481_ = lean_ctor_get_uint64(v_x_1473_, sizeof(void*)*2);
v___y_1476_ = v_hash_1481_;
goto v___jp_1475_;
}
v___jp_1475_:
{
size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = lean_uint64_to_usize(v___y_1476_);
v___x_1478_ = ((size_t)1ULL);
v___x_1479_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1472_, v___x_1477_, v___x_1478_, v_x_1473_, v_x_1474_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1482_, lean_object* v_as_1483_, size_t v_i_1484_, size_t v_stop_1485_, lean_object* v_b_1486_){
_start:
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_usize_dec_eq(v_i_1484_, v_stop_1485_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; 
v___x_1488_ = lean_array_uget_borrowed(v_as_1483_, v_i_1484_);
lean_inc(v_declName_1482_);
lean_inc(v___x_1488_);
v___x_1489_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1486_, v___x_1488_, v_declName_1482_);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = lean_usize_add(v_i_1484_, v___x_1490_);
v_i_1484_ = v___x_1491_;
v_b_1486_ = v___x_1489_;
goto _start;
}
else
{
lean_dec(v_declName_1482_);
return v_b_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1493_, lean_object* v_as_1494_, lean_object* v_i_1495_, lean_object* v_stop_1496_, lean_object* v_b_1497_){
_start:
{
size_t v_i_boxed_1498_; size_t v_stop_boxed_1499_; lean_object* v_res_1500_; 
v_i_boxed_1498_ = lean_unbox_usize(v_i_1495_);
lean_dec(v_i_1495_);
v_stop_boxed_1499_ = lean_unbox_usize(v_stop_1496_);
lean_dec(v_stop_1496_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1493_, v_as_1494_, v_i_boxed_1498_, v_stop_boxed_1499_, v_b_1497_);
lean_dec_ref(v_as_1494_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1501_, lean_object* v_declName_1502_, lean_object* v_s_1503_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_array_get_size(v_eqThms_1501_);
v___x_1506_ = lean_nat_dec_lt(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_dec(v_declName_1502_);
return v_s_1503_;
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_nat_dec_le(v___x_1505_, v___x_1505_);
if (v___x_1507_ == 0)
{
if (v___x_1506_ == 0)
{
lean_dec(v_declName_1502_);
return v_s_1503_;
}
else
{
size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = lean_usize_of_nat(v___x_1505_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1502_, v_eqThms_1501_, v___x_1508_, v___x_1509_, v_s_1503_);
return v___x_1510_;
}
}
else
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = lean_usize_of_nat(v___x_1505_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1502_, v_eqThms_1501_, v___x_1511_, v___x_1512_, v_s_1503_);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1514_, lean_object* v_declName_1515_, lean_object* v_s_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1514_, v_declName_1515_, v_s_1516_);
lean_dec_ref(v_eqThms_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1518_, lean_object* v_eqThms_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v_env_1523_; lean_object* v_nextMacroScope_1524_; lean_object* v_ngen_1525_; lean_object* v_auxDeclNGen_1526_; lean_object* v_traceState_1527_; lean_object* v_messages_1528_; lean_object* v_infoState_1529_; lean_object* v_snapshotTasks_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1546_; 
v___x_1522_ = lean_st_ref_take(v_a_1520_);
v_env_1523_ = lean_ctor_get(v___x_1522_, 0);
v_nextMacroScope_1524_ = lean_ctor_get(v___x_1522_, 1);
v_ngen_1525_ = lean_ctor_get(v___x_1522_, 2);
v_auxDeclNGen_1526_ = lean_ctor_get(v___x_1522_, 3);
v_traceState_1527_ = lean_ctor_get(v___x_1522_, 4);
v_messages_1528_ = lean_ctor_get(v___x_1522_, 6);
v_infoState_1529_ = lean_ctor_get(v___x_1522_, 7);
v_snapshotTasks_1530_ = lean_ctor_get(v___x_1522_, 8);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1522_, 5);
lean_dec(v_unused_1547_);
v___x_1532_ = v___x_1522_;
v_isShared_1533_ = v_isSharedCheck_1546_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_snapshotTasks_1530_);
lean_inc(v_infoState_1529_);
lean_inc(v_messages_1528_);
lean_inc(v_traceState_1527_);
lean_inc(v_auxDeclNGen_1526_);
lean_inc(v_ngen_1525_);
lean_inc(v_nextMacroScope_1524_);
lean_inc(v_env_1523_);
lean_dec(v___x_1522_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1546_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v_asyncMode_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1534_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1535_ = lean_ctor_get(v___x_1534_, 2);
v___f_1536_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1536_, 0, v_eqThms_1519_);
lean_closure_set(v___f_1536_, 1, v_declName_1518_);
v___x_1537_ = lean_box(0);
v___x_1538_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1534_, v_env_1523_, v___f_1536_, v_asyncMode_1535_, v___x_1537_);
v___x_1539_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 5, v___x_1539_);
lean_ctor_set(v___x_1532_, 0, v___x_1538_);
v___x_1541_ = v___x_1532_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_nextMacroScope_1524_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_ngen_1525_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_auxDeclNGen_1526_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_traceState_1527_);
lean_ctor_set(v_reuseFailAlloc_1545_, 5, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1545_, 6, v_messages_1528_);
lean_ctor_set(v_reuseFailAlloc_1545_, 7, v_infoState_1529_);
lean_ctor_set(v_reuseFailAlloc_1545_, 8, v_snapshotTasks_1530_);
v___x_1541_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_st_ref_put(v_a_1520_, v___x_1541_);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1548_, lean_object* v_eqThms_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1548_, v_eqThms_1549_, v_a_1550_);
lean_dec(v_a_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1553_, lean_object* v_eqThms_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1553_, v_eqThms_1554_, v_a_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1559_, lean_object* v_eqThms_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1559_, v_eqThms_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1566_, v_x_1567_, v_x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1570_, lean_object* v_x_1571_, size_t v_x_1572_, size_t v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1571_, v_x_1572_, v_x_1573_, v_x_1574_, v_x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1577_, lean_object* v_x_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_){
_start:
{
size_t v_x_887__boxed_1583_; size_t v_x_888__boxed_1584_; lean_object* v_res_1585_; 
v_x_887__boxed_1583_ = lean_unbox_usize(v_x_1579_);
lean_dec(v_x_1579_);
v_x_888__boxed_1584_ = lean_unbox_usize(v_x_1580_);
lean_dec(v_x_1580_);
v_res_1585_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1577_, v_x_1578_, v_x_887__boxed_1583_, v_x_888__boxed_1584_, v_x_1581_, v_x_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1586_, lean_object* v_n_1587_, lean_object* v_k_1588_, lean_object* v_v_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1587_, v_k_1588_, v_v_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1591_, size_t v_depth_1592_, lean_object* v_keys_1593_, lean_object* v_vals_1594_, lean_object* v_heq_1595_, lean_object* v_i_1596_, lean_object* v_entries_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1592_, v_keys_1593_, v_vals_1594_, v_i_1596_, v_entries_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1599_, lean_object* v_depth_1600_, lean_object* v_keys_1601_, lean_object* v_vals_1602_, lean_object* v_heq_1603_, lean_object* v_i_1604_, lean_object* v_entries_1605_){
_start:
{
size_t v_depth_boxed_1606_; lean_object* v_res_1607_; 
v_depth_boxed_1606_ = lean_unbox_usize(v_depth_1600_);
lean_dec(v_depth_1600_);
v_res_1607_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1599_, v_depth_boxed_1606_, v_keys_1601_, v_vals_1602_, v_heq_1603_, v_i_1604_, v_entries_1605_);
lean_dec_ref(v_vals_1602_);
lean_dec_ref(v_keys_1601_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1609_, v_x_1610_, v_x_1611_, v_x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1614_, lean_object* v_env_1615_, lean_object* v_idx_1616_, lean_object* v_eqs_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v_nextEq_1624_; uint8_t v___x_1625_; 
v___x_1619_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_nat_add(v_idx_1616_, v___x_1620_);
lean_dec(v_idx_1616_);
lean_inc(v___x_1621_);
v___x_1622_ = l_Nat_reprFast(v___x_1621_);
v___x_1623_ = lean_string_append(v___x_1619_, v___x_1622_);
lean_dec_ref(v___x_1622_);
lean_inc(v_declName_1614_);
lean_inc_ref(v_env_1615_);
v_nextEq_1624_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1615_, v_declName_1614_, v___x_1623_);
v___x_1625_ = l_Lean_Environment_containsOnBranch(v_env_1615_, v_nextEq_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
lean_dec(v_nextEq_1624_);
lean_dec(v___x_1621_);
lean_dec_ref(v_env_1615_);
lean_dec(v_declName_1614_);
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v_eqs_1617_);
return v___x_1626_;
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_array_push(v_eqs_1617_, v_nextEq_1624_);
v_idx_1616_ = v___x_1621_;
v_eqs_1617_ = v___x_1627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1629_, lean_object* v_env_1630_, lean_object* v_idx_1631_, lean_object* v_eqs_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1629_, v_env_1630_, v_idx_1631_, v_eqs_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1635_, lean_object* v_env_1636_, lean_object* v_idx_1637_, lean_object* v_eqs_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1635_, v_env_1636_, v_idx_1637_, v_eqs_1638_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1645_, lean_object* v_env_1646_, lean_object* v_idx_1647_, lean_object* v_eqs_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1645_, v_env_1646_, v_idx_1647_, v_eqs_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1658_; lean_object* v_env_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; uint8_t v___x_1663_; 
v___x_1658_ = lean_st_ref_get(v_a_1656_);
v_env_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc_ref_n(v_env_1659_, 3);
lean_dec(v___x_1658_);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1655_);
v___x_1661_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1659_, v_declName_1655_, v___x_1660_);
v___x_1662_ = 1;
lean_inc(v___x_1661_);
v___x_1663_ = l_Lean_Environment_contains(v_env_1659_, v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1661_);
lean_dec_ref(v_env_1659_);
lean_dec(v_declName_1655_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_mk_empty_array_with_capacity(v___x_1666_);
v___x_1668_ = lean_array_push(v___x_1667_, v___x_1661_);
lean_inc(v_declName_1655_);
v___x_1669_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1655_, v_env_1659_, v___x_1666_, v___x_1668_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1679_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc_n(v_a_1670_, 2);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1655_, v_a_1670_, v_a_1656_);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v___x_1671_, 0);
lean_dec(v_unused_1680_);
v___x_1673_ = v___x_1671_;
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
else
{
lean_dec(v___x_1671_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v_a_1670_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1675_);
v___x_1677_ = v___x_1673_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_declName_1655_);
v_a_1681_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1669_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1669_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1689_, v_a_1690_);
lean_dec(v_a_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1693_, v_a_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1707_, lean_object* v_localInsts_1708_, lean_object* v_x_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1707_, v_localInsts_1708_, v_x_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_a_1724_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1715_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1715_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1732_, lean_object* v_localInsts_1733_, lean_object* v_x_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1732_, v_localInsts_1733_, v_x_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1741_, lean_object* v_lctx_1742_, lean_object* v_localInsts_1743_, lean_object* v_x_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1742_, v_localInsts_1743_, v_x_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1751_, lean_object* v_lctx_1752_, lean_object* v_localInsts_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1751_, v_lctx_1752_, v_localInsts_1753_, v_x_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1764_, lean_object* v_as_x27_1765_, lean_object* v_b_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
if (lean_obj_tag(v_as_x27_1765_) == 0)
{
lean_object* v___x_1772_; 
lean_dec(v_declName_1764_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_b_1766_);
return v___x_1772_;
}
else
{
lean_object* v_head_1773_; lean_object* v_tail_1774_; lean_object* v___x_1775_; 
lean_dec_ref(v_b_1766_);
v_head_1773_ = lean_ctor_get(v_as_x27_1765_, 0);
v_tail_1774_ = lean_ctor_get(v_as_x27_1765_, 1);
lean_inc(v_head_1773_);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1769_);
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v_declName_1764_);
v___x_1775_ = lean_apply_6(v_head_1773_, v_declName_1764_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, lean_box(0));
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1777_ = lean_box(0);
if (lean_obj_tag(v_a_1776_) == 1)
{
lean_object* v_val_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1788_; 
v_val_1778_ = lean_ctor_get(v_a_1776_, 0);
lean_inc(v_val_1778_);
v___x_1779_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1764_, v_val_1778_, v___y_1770_);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1789_);
v___x_1781_ = v___x_1779_;
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
else
{
lean_dec(v___x_1779_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_a_1776_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v___x_1777_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1784_);
v___x_1786_ = v___x_1781_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v___x_1790_; 
lean_dec(v_a_1776_);
v___x_1790_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1765_ = v_tail_1774_;
v_b_1766_ = v___x_1790_;
goto _start;
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_declName_1764_);
v_a_1792_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1775_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1775_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1800_, lean_object* v_as_x27_1801_, lean_object* v_b_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1800_, v_as_x27_1801_, v_b_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v_as_x27_1801_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
lean_inc(v_declName_1809_);
v___x_1815_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1853_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1853_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1853_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_unbox(v_a_1816_);
lean_dec(v_a_1816_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_dec(v_declName_1809_);
v___x_1821_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1821_);
v___x_1823_ = v___x_1818_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
else
{
lean_object* v___x_1825_; 
lean_del_object(v___x_1818_);
lean_inc(v_declName_1809_);
v___x_1825_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1809_, v___y_1813_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
if (lean_obj_tag(v_a_1826_) == 1)
{
lean_dec_ref_known(v_a_1826_, 1);
lean_dec(v_declName_1809_);
return v___x_1825_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref_known(v___x_1825_, 1);
lean_dec(v_a_1826_);
v___x_1827_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1828_ = lean_st_ref_get(v___x_1827_);
v___x_1829_ = lean_box(0);
v___x_1830_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1831_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1809_, v___x_1828_, v___x_1830_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___x_1828_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1844_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_fst_1836_; 
v_fst_1836_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_fst_1836_);
lean_dec(v_a_1832_);
if (lean_obj_tag(v_fst_1836_) == 0)
{
lean_object* v___x_1838_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1829_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1829_);
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
lean_object* v_val_1840_; lean_object* v___x_1842_; 
v_val_1840_ = lean_ctor_get(v_fst_1836_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v_fst_1836_, 1);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v_val_1840_);
v___x_1842_ = v___x_1834_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_val_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
v_a_1845_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1831_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1831_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
else
{
lean_dec(v_declName_1809_);
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_declName_1809_);
v_a_1854_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1815_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1815_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1868_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1869_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1872_ = lean_box(1);
v___x_1873_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1874_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1873_);
lean_ctor_set(v___x_1875_, 2, v___x_1872_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v___f_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___f_1884_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1884_, 0, v_declName_1878_);
v___x_1885_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1887_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1885_, v___x_1886_, v___f_1884_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1895_, lean_object* v_as_1896_, lean_object* v_as_x27_1897_, lean_object* v_b_1898_, lean_object* v_a_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1895_, v_as_x27_1897_, v_b_1898_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1906_, lean_object* v_as_1907_, lean_object* v_as_x27_1908_, lean_object* v_b_1909_, lean_object* v_a_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1906_, v_as_1907_, v_as_x27_1908_, v_b_1909_, v_a_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v_as_x27_1908_);
lean_dec(v_as_1907_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1923_ = lean_unsigned_to_nat(32u);
v___x_1924_ = lean_mk_empty_array_with_capacity(v___x_1923_);
lean_dec_ref(v___x_1924_);
v___x_1925_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1926_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1917_);
v___x_1927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1927_, 0, v_declName_1917_);
v___x_1928_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1928_, 0, lean_box(0));
lean_closure_set(v___x_1928_, 1, v_declName_1917_);
lean_closure_set(v___x_1928_, 2, v___x_1927_);
v___x_1929_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1925_, v___x_1926_, v___x_1928_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_env_1944_; lean_object* v___x_1945_; lean_object* v_toCold_1946_; lean_object* v_mctx_1947_; lean_object* v_lctx_1948_; lean_object* v_options_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1943_ = lean_st_ref_get(v___y_1941_);
v_env_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc_ref(v_env_1944_);
lean_dec(v___x_1943_);
v___x_1945_ = lean_st_ref_get(v___y_1939_);
v_toCold_1946_ = lean_ctor_get(v___y_1940_, 0);
v_mctx_1947_ = lean_ctor_get(v___x_1945_, 0);
lean_inc_ref(v_mctx_1947_);
lean_dec(v___x_1945_);
v_lctx_1948_ = lean_ctor_get(v___y_1938_, 2);
v_options_1949_ = lean_ctor_get(v_toCold_1946_, 2);
lean_inc_ref(v_options_1949_);
lean_inc_ref(v_lctx_1948_);
v___x_1950_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1950_, 0, v_env_1944_);
lean_ctor_set(v___x_1950_, 1, v_mctx_1947_);
lean_ctor_set(v___x_1950_, 2, v_lctx_1948_);
lean_ctor_set(v___x_1950_, 3, v_options_1949_);
v___x_1951_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v_msgData_1937_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1959_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1960_; double v___x_1961_; 
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_float_of_nat(v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1965_, lean_object* v_msg_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_ref_1972_; lean_object* v___x_1973_; lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2018_; 
v_ref_1972_ = lean_ctor_get(v___y_1969_, 2);
v___x_1973_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_2018_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2018_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v_traceState_1979_; lean_object* v_env_1980_; lean_object* v_nextMacroScope_1981_; lean_object* v_ngen_1982_; lean_object* v_auxDeclNGen_1983_; lean_object* v_cache_1984_; lean_object* v_messages_1985_; lean_object* v_infoState_1986_; lean_object* v_snapshotTasks_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2017_; 
v___x_1978_ = lean_st_ref_take(v___y_1970_);
v_traceState_1979_ = lean_ctor_get(v___x_1978_, 4);
v_env_1980_ = lean_ctor_get(v___x_1978_, 0);
v_nextMacroScope_1981_ = lean_ctor_get(v___x_1978_, 1);
v_ngen_1982_ = lean_ctor_get(v___x_1978_, 2);
v_auxDeclNGen_1983_ = lean_ctor_get(v___x_1978_, 3);
v_cache_1984_ = lean_ctor_get(v___x_1978_, 5);
v_messages_1985_ = lean_ctor_get(v___x_1978_, 6);
v_infoState_1986_ = lean_ctor_get(v___x_1978_, 7);
v_snapshotTasks_1987_ = lean_ctor_get(v___x_1978_, 8);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1989_ = v___x_1978_;
v_isShared_1990_ = v_isSharedCheck_2017_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snapshotTasks_1987_);
lean_inc(v_infoState_1986_);
lean_inc(v_messages_1985_);
lean_inc(v_cache_1984_);
lean_inc(v_traceState_1979_);
lean_inc(v_auxDeclNGen_1983_);
lean_inc(v_ngen_1982_);
lean_inc(v_nextMacroScope_1981_);
lean_inc(v_env_1980_);
lean_dec(v___x_1978_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2017_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
uint64_t v_tid_1991_; lean_object* v_traces_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2016_; 
v_tid_1991_ = lean_ctor_get_uint64(v_traceState_1979_, sizeof(void*)*1);
v_traces_1992_ = lean_ctor_get(v_traceState_1979_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_traceState_1979_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1994_ = v_traceState_1979_;
v_isShared_1995_ = v_isSharedCheck_2016_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_traces_1992_);
lean_dec(v_traceState_1979_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2016_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; double v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_1998_ = 0;
v___x_1999_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_2000_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2000_, 0, v_cls_1965_);
lean_ctor_set(v___x_2000_, 1, v___x_1996_);
lean_ctor_set(v___x_2000_, 2, v___x_1999_);
lean_ctor_set_float(v___x_2000_, sizeof(void*)*3, v___x_1997_);
lean_ctor_set_float(v___x_2000_, sizeof(void*)*3 + 8, v___x_1997_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*3 + 16, v___x_1998_);
v___x_2001_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_2002_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v_a_1974_);
lean_ctor_set(v___x_2002_, 2, v___x_2001_);
lean_inc(v_ref_1972_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v_ref_1972_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = l_Lean_PersistentArray_push___redArg(v_traces_1992_, v___x_2003_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2004_);
v___x_2006_ = v___x_1994_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2004_);
lean_ctor_set_uint64(v_reuseFailAlloc_2015_, sizeof(void*)*1, v_tid_1991_);
v___x_2006_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 4, v___x_2006_);
v___x_2008_ = v___x_1989_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_env_1980_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_nextMacroScope_1981_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_ngen_1982_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_auxDeclNGen_1983_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_cache_1984_);
lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_messages_1985_);
lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_infoState_1986_);
lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_snapshotTasks_1987_);
v___x_2008_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2009_ = lean_st_ref_put(v___y_1970_, v___x_2008_);
v___x_2010_ = lean_box(0);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_2010_);
v___x_2012_ = v___x_1976_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2019_, lean_object* v_msg_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2019_, v_msg_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2027_, lean_object* v_as_2028_, size_t v_sz_2029_, size_t v_i_2030_, lean_object* v_b_2031_){
_start:
{
lean_object* v_a_2034_; uint8_t v___x_2038_; 
v___x_2038_ = lean_usize_dec_lt(v_i_2030_, v_sz_2029_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_b_2031_);
return v___x_2039_;
}
else
{
lean_object* v_a_2040_; lean_object* v_defValue_2041_; uint8_t v___x_2042_; uint8_t v___y_2056_; uint8_t v___x_2057_; 
v_a_2040_ = lean_array_uget(v_as_2028_, v_i_2030_);
v_defValue_2041_ = lean_ctor_get(v_a_2040_, 1);
v___x_2042_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2027_, v_a_2040_);
v___x_2057_ = lean_unbox(v_defValue_2041_);
if (v___x_2057_ == 0)
{
if (v___x_2042_ == 0)
{
v___y_2056_ = v___x_2038_;
goto v___jp_2055_;
}
else
{
goto v___jp_2043_;
}
}
else
{
v___y_2056_ = v___x_2042_;
goto v___jp_2055_;
}
v___jp_2043_:
{
lean_object* v_name_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2053_; 
v_name_2044_ = lean_ctor_get(v_a_2040_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v_a_2040_, 1);
lean_dec(v_unused_2054_);
v___x_2046_ = v_a_2040_;
v_isShared_2047_ = v_isSharedCheck_2053_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_name_2044_);
lean_dec(v_a_2040_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2053_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2048_, 0, v___x_2042_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___x_2048_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_name_2044_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_array_push(v_b_2031_, v___x_2050_);
v_a_2034_ = v___x_2051_;
goto v___jp_2033_;
}
}
}
v___jp_2055_:
{
if (v___y_2056_ == 0)
{
goto v___jp_2043_;
}
else
{
lean_dec(v_a_2040_);
v_a_2034_ = v_b_2031_;
goto v___jp_2033_;
}
}
}
v___jp_2033_:
{
size_t v___x_2035_; size_t v___x_2036_; 
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2030_, v___x_2035_);
v_i_2030_ = v___x_2036_;
v_b_2031_ = v_a_2034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2058_, lean_object* v_as_2059_, lean_object* v_sz_2060_, lean_object* v_i_2061_, lean_object* v_b_2062_, lean_object* v___y_2063_){
_start:
{
size_t v_sz_boxed_2064_; size_t v_i_boxed_2065_; lean_object* v_res_2066_; 
v_sz_boxed_2064_ = lean_unbox_usize(v_sz_2060_);
lean_dec(v_sz_2060_);
v_i_boxed_2065_ = lean_unbox_usize(v_i_2061_);
lean_dec(v_i_2061_);
v_res_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2058_, v_as_2059_, v_sz_boxed_2064_, v_i_boxed_2065_, v_b_2062_);
lean_dec_ref(v_as_2059_);
lean_dec_ref(v___x_2058_);
return v_res_2066_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2069_; size_t v_sz_2070_; 
v___x_2069_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2070_ = lean_array_size(v___x_2069_);
return v_sz_2070_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2072_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
lean_ctor_set(v___x_2072_, 2, v___x_2071_);
lean_ctor_set(v___x_2072_, 3, v___x_2071_);
lean_ctor_set(v___x_2072_, 4, v___x_2071_);
lean_ctor_set(v___x_2072_, 5, v___x_2071_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2081_ = l_Lean_Name_append(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2084_ = l_Lean_stringToMessageData(v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_toCold_2091_; lean_object* v_options_2092_; lean_object* v_inheritedTraceOptions_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; size_t v_sz_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v_toCold_2091_ = lean_ctor_get(v_a_2088_, 0);
v_options_2092_ = lean_ctor_get(v_toCold_2091_, 2);
v_inheritedTraceOptions_2093_ = lean_ctor_get(v_toCold_2091_, 11);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2096_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2097_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2098_ = ((size_t)0ULL);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2092_, v___x_2096_, v_sz_2097_, v___x_2098_, v___x_2095_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2159_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2159_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2159_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = lean_array_get_size(v_a_2100_);
v___x_2148_ = lean_nat_dec_eq(v___x_2147_, v___x_2094_);
if (v___x_2148_ == 0)
{
uint8_t v_hasTrace_2149_; 
v_hasTrace_2149_ = lean_ctor_get_uint8(v_options_2092_, sizeof(void*)*1);
if (v_hasTrace_2149_ == 0)
{
v___y_2105_ = v_a_2087_;
v___y_2106_ = v_a_2089_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2150_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2151_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2152_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2093_, v_options_2092_, v___x_2151_);
if (v___x_2152_ == 0)
{
v___y_2105_ = v_a_2087_;
v___y_2106_ = v_a_2089_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2153_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2085_);
v___x_2154_ = l_Lean_MessageData_ofName(v_declName_2085_);
v___x_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2150_, v___x_2155_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_dec_ref_known(v___x_2156_, 1);
v___y_2105_ = v_a_2087_;
v___y_2106_ = v_a_2089_;
goto v___jp_2104_;
}
else
{
lean_del_object(v___x_2102_);
lean_dec(v_a_2100_);
lean_dec(v_declName_2085_);
return v___x_2156_;
}
}
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_del_object(v___x_2102_);
lean_dec(v_a_2100_);
lean_dec(v_declName_2085_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
v___jp_2104_:
{
lean_object* v___x_2107_; lean_object* v_env_2108_; lean_object* v_nextMacroScope_2109_; lean_object* v_ngen_2110_; lean_object* v_auxDeclNGen_2111_; lean_object* v_traceState_2112_; lean_object* v_messages_2113_; lean_object* v_infoState_2114_; lean_object* v_snapshotTasks_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2145_; 
v___x_2107_ = lean_st_ref_take(v___y_2106_);
v_env_2108_ = lean_ctor_get(v___x_2107_, 0);
v_nextMacroScope_2109_ = lean_ctor_get(v___x_2107_, 1);
v_ngen_2110_ = lean_ctor_get(v___x_2107_, 2);
v_auxDeclNGen_2111_ = lean_ctor_get(v___x_2107_, 3);
v_traceState_2112_ = lean_ctor_get(v___x_2107_, 4);
v_messages_2113_ = lean_ctor_get(v___x_2107_, 6);
v_infoState_2114_ = lean_ctor_get(v___x_2107_, 7);
v_snapshotTasks_2115_ = lean_ctor_get(v___x_2107_, 8);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v___x_2107_, 5);
lean_dec(v_unused_2146_);
v___x_2117_ = v___x_2107_;
v_isShared_2118_ = v_isSharedCheck_2145_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_snapshotTasks_2115_);
lean_inc(v_infoState_2114_);
lean_inc(v_messages_2113_);
lean_inc(v_traceState_2112_);
lean_inc(v_auxDeclNGen_2111_);
lean_inc(v_ngen_2110_);
lean_inc(v_nextMacroScope_2109_);
lean_inc(v_env_2108_);
lean_dec(v___x_2107_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2145_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2119_ = l_Lean_Meta_eqnOptionsExt;
v___x_2120_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2119_, v_env_2108_, v_declName_2085_, v_a_2100_);
v___x_2121_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 5, v___x_2121_);
lean_ctor_set(v___x_2117_, 0, v___x_2120_);
v___x_2123_ = v___x_2117_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_nextMacroScope_2109_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_ngen_2110_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_auxDeclNGen_2111_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_traceState_2112_);
lean_ctor_set(v_reuseFailAlloc_2144_, 5, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2144_, 6, v_messages_2113_);
lean_ctor_set(v_reuseFailAlloc_2144_, 7, v_infoState_2114_);
lean_ctor_set(v_reuseFailAlloc_2144_, 8, v_snapshotTasks_2115_);
v___x_2123_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_mctx_2126_; lean_object* v_zetaDeltaFVarIds_2127_; lean_object* v_postponed_2128_; lean_object* v_diag_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2142_; 
v___x_2124_ = lean_st_ref_put(v___y_2106_, v___x_2123_);
v___x_2125_ = lean_st_ref_take(v___y_2105_);
v_mctx_2126_ = lean_ctor_get(v___x_2125_, 0);
v_zetaDeltaFVarIds_2127_ = lean_ctor_get(v___x_2125_, 2);
v_postponed_2128_ = lean_ctor_get(v___x_2125_, 3);
v_diag_2129_ = lean_ctor_get(v___x_2125_, 4);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v___x_2125_, 1);
lean_dec(v_unused_2143_);
v___x_2131_ = v___x_2125_;
v_isShared_2132_ = v_isSharedCheck_2142_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_diag_2129_);
lean_inc(v_postponed_2128_);
lean_inc(v_zetaDeltaFVarIds_2127_);
lean_inc(v_mctx_2126_);
lean_dec(v___x_2125_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2142_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 1, v___x_2133_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_mctx_2126_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_zetaDeltaFVarIds_2127_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_postponed_2128_);
lean_ctor_set(v_reuseFailAlloc_2141_, 4, v_diag_2129_);
v___x_2135_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2136_ = lean_st_ref_put(v___y_2105_, v___x_2135_);
v___x_2137_ = lean_box(0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2137_);
v___x_2139_ = v___x_2102_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
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
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_declName_2085_);
v_a_2160_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2099_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2099_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2175_, lean_object* v_as_2176_, size_t v_sz_2177_, size_t v_i_2178_, lean_object* v_b_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2175_, v_as_2176_, v_sz_2177_, v_i_2178_, v_b_2179_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2186_, lean_object* v_as_2187_, lean_object* v_sz_2188_, lean_object* v_i_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
size_t v_sz_boxed_2196_; size_t v_i_boxed_2197_; lean_object* v_res_2198_; 
v_sz_boxed_2196_ = lean_unbox_usize(v_sz_2188_);
lean_dec(v_sz_2188_);
v_i_boxed_2197_ = lean_unbox_usize(v_i_2189_);
lean_dec(v_i_2189_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2186_, v_as_2187_, v_sz_boxed_2196_, v_i_boxed_2197_, v_b_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_as_2187_);
lean_dec_ref(v___x_2186_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_st_mk_ref(v___x_2200_);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2205_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = l_Lean_initializing();
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec_ref(v_f_2205_);
v___x_2208_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2210_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2211_ = lean_st_ref_take(v___x_2210_);
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v_f_2205_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_st_ref_put(v___x_2210_, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2221_, lean_object* v_as_x27_2222_, lean_object* v_b_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
if (lean_obj_tag(v_as_x27_2222_) == 0)
{
lean_object* v___x_2229_; 
lean_dec(v_declName_2221_);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_b_2223_);
return v___x_2229_;
}
else
{
lean_object* v_head_2230_; lean_object* v_tail_2231_; lean_object* v___x_2232_; 
lean_dec_ref(v_b_2223_);
v_head_2230_ = lean_ctor_get(v_as_x27_2222_, 0);
v_tail_2231_ = lean_ctor_get(v_as_x27_2222_, 1);
lean_inc(v_head_2230_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v___y_2225_);
lean_inc_ref(v___y_2224_);
lean_inc(v_declName_2221_);
v___x_2232_ = lean_apply_6(v_head_2230_, v_declName_2221_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, lean_box(0));
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2245_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2245_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2245_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_box(0);
if (lean_obj_tag(v_a_2233_) == 1)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec(v_declName_2221_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v_a_2233_);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2237_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2239_);
v___x_2241_ = v___x_2235_;
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
else
{
lean_object* v___x_2243_; 
lean_del_object(v___x_2235_);
lean_dec(v_a_2233_);
v___x_2243_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2222_ = v_tail_2231_;
v_b_2223_ = v___x_2243_;
goto _start;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_declName_2221_);
v_a_2246_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2232_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2232_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2254_, lean_object* v_as_x27_2255_, lean_object* v_b_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2254_, v_as_x27_2255_, v_b_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v_as_x27_2255_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2263_, lean_object* v_declName_2264_, uint8_t v_nonRec_2265_, lean_object* v___x_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2275_; lean_object* v_env_2276_; uint8_t v___x_2277_; uint8_t v___x_2278_; 
v___x_2275_ = lean_st_ref_get(v___y_2270_);
v_env_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc_ref(v_env_2276_);
lean_dec(v___x_2275_);
v___x_2277_ = 1;
lean_inc(v___x_2263_);
v___x_2278_ = l_Lean_Environment_contains(v_env_2276_, v___x_2263_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; 
lean_dec(v___x_2263_);
lean_inc(v_declName_2264_);
v___x_2279_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2264_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; uint8_t v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
if (v___x_2281_ == 0)
{
lean_dec_ref(v___x_2266_);
lean_dec(v_declName_2264_);
goto v___jp_2272_;
}
else
{
lean_object* v___x_2282_; 
lean_inc(v_declName_2264_);
v___x_2282_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2264_, v___y_2270_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; uint8_t v___x_2284_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = lean_unbox(v_a_2283_);
lean_dec(v_a_2283_);
if (v___x_2284_ == 0)
{
if (v_nonRec_2265_ == 0)
{
lean_dec_ref(v___x_2266_);
lean_dec(v_declName_2264_);
goto v___jp_2272_;
}
else
{
lean_object* v___x_2285_; lean_object* v_env_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2285_ = lean_st_ref_get(v___y_2270_);
v_env_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_env_2286_);
lean_dec(v___x_2285_);
lean_inc(v_declName_2264_);
v___x_2287_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2286_, v_declName_2264_, v___x_2266_);
v___x_2288_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2264_, v___x_2287_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2288_;
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec_ref(v___x_2266_);
v___x_2289_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2290_ = lean_st_ref_get(v___x_2289_);
v___x_2291_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2292_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2264_, v___x_2290_, v___x_2291_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___x_2290_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2302_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2302_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2302_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_fst_2297_; 
v_fst_2297_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_fst_2297_);
lean_dec(v_a_2293_);
if (lean_obj_tag(v_fst_2297_) == 0)
{
lean_del_object(v___x_2295_);
goto v___jp_2272_;
}
else
{
lean_object* v_val_2298_; lean_object* v___x_2300_; 
v_val_2298_ = lean_ctor_get(v_fst_2297_, 0);
lean_inc(v_val_2298_);
lean_dec_ref_known(v_fst_2297_, 1);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v_val_2298_);
v___x_2300_ = v___x_2295_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_val_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
v_a_2303_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2292_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2292_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v___x_2266_);
lean_dec(v_declName_2264_);
v_a_2311_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2282_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2282_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v___x_2266_);
lean_dec(v_declName_2264_);
v_a_2319_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2279_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2279_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec_ref(v___x_2266_);
lean_dec(v_declName_2264_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2263_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
v___jp_2272_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2329_, lean_object* v_declName_2330_, lean_object* v_nonRec_2331_, lean_object* v___x_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
uint8_t v_nonRec_boxed_2338_; lean_object* v_res_2339_; 
v_nonRec_boxed_2338_ = lean_unbox(v_nonRec_2331_);
v_res_2339_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2329_, v_declName_2330_, v_nonRec_boxed_2338_, v___x_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_ref_2346_; lean_object* v___x_2347_; lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2356_; 
v_ref_2346_ = lean_ctor_get(v___y_2343_, 2);
v___x_2347_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_inc(v_ref_2346_);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v_ref_2346_);
lean_ctor_set(v___x_2352_, 1, v_a_2348_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set_tag(v___x_2350_, 1);
lean_ctor_set(v___x_2350_, 0, v___x_2352_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2364_, uint8_t v_isExporting_2365_, lean_object* v___x_2366_, lean_object* v___y_2367_, lean_object* v___x_2368_, lean_object* v_a_x3f_2369_){
_start:
{
lean_object* v___x_2371_; lean_object* v_env_2372_; lean_object* v_nextMacroScope_2373_; lean_object* v_ngen_2374_; lean_object* v_auxDeclNGen_2375_; lean_object* v_traceState_2376_; lean_object* v_messages_2377_; lean_object* v_infoState_2378_; lean_object* v_snapshotTasks_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2404_; 
v___x_2371_ = lean_st_ref_take(v___y_2364_);
v_env_2372_ = lean_ctor_get(v___x_2371_, 0);
v_nextMacroScope_2373_ = lean_ctor_get(v___x_2371_, 1);
v_ngen_2374_ = lean_ctor_get(v___x_2371_, 2);
v_auxDeclNGen_2375_ = lean_ctor_get(v___x_2371_, 3);
v_traceState_2376_ = lean_ctor_get(v___x_2371_, 4);
v_messages_2377_ = lean_ctor_get(v___x_2371_, 6);
v_infoState_2378_ = lean_ctor_get(v___x_2371_, 7);
v_snapshotTasks_2379_ = lean_ctor_get(v___x_2371_, 8);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; 
v_unused_2405_ = lean_ctor_get(v___x_2371_, 5);
lean_dec(v_unused_2405_);
v___x_2381_ = v___x_2371_;
v_isShared_2382_ = v_isSharedCheck_2404_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_snapshotTasks_2379_);
lean_inc(v_infoState_2378_);
lean_inc(v_messages_2377_);
lean_inc(v_traceState_2376_);
lean_inc(v_auxDeclNGen_2375_);
lean_inc(v_ngen_2374_);
lean_inc(v_nextMacroScope_2373_);
lean_inc(v_env_2372_);
lean_dec(v___x_2371_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2404_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = l_Lean_Environment_setExporting(v_env_2372_, v_isExporting_2365_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 5, v___x_2366_);
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_nextMacroScope_2373_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_ngen_2374_);
lean_ctor_set(v_reuseFailAlloc_2403_, 3, v_auxDeclNGen_2375_);
lean_ctor_set(v_reuseFailAlloc_2403_, 4, v_traceState_2376_);
lean_ctor_set(v_reuseFailAlloc_2403_, 5, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2403_, 6, v_messages_2377_);
lean_ctor_set(v_reuseFailAlloc_2403_, 7, v_infoState_2378_);
lean_ctor_set(v_reuseFailAlloc_2403_, 8, v_snapshotTasks_2379_);
v___x_2385_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v_mctx_2388_; lean_object* v_zetaDeltaFVarIds_2389_; lean_object* v_postponed_2390_; lean_object* v_diag_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2401_; 
v___x_2386_ = lean_st_ref_put(v___y_2364_, v___x_2385_);
v___x_2387_ = lean_st_ref_take(v___y_2367_);
v_mctx_2388_ = lean_ctor_get(v___x_2387_, 0);
v_zetaDeltaFVarIds_2389_ = lean_ctor_get(v___x_2387_, 2);
v_postponed_2390_ = lean_ctor_get(v___x_2387_, 3);
v_diag_2391_ = lean_ctor_get(v___x_2387_, 4);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; 
v_unused_2402_ = lean_ctor_get(v___x_2387_, 1);
lean_dec(v_unused_2402_);
v___x_2393_ = v___x_2387_;
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_diag_2391_);
lean_inc(v_postponed_2390_);
lean_inc(v_zetaDeltaFVarIds_2389_);
lean_inc(v_mctx_2388_);
lean_dec(v___x_2387_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2368_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_mctx_2388_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_zetaDeltaFVarIds_2389_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_postponed_2390_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_diag_2391_);
v___x_2396_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = lean_st_ref_put(v___y_2367_, v___x_2396_);
v___x_2398_ = lean_box(0);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2406_, lean_object* v_isExporting_2407_, lean_object* v___x_2408_, lean_object* v___y_2409_, lean_object* v___x_2410_, lean_object* v_a_x3f_2411_, lean_object* v___y_2412_){
_start:
{
uint8_t v_isExporting_boxed_2413_; lean_object* v_res_2414_; 
v_isExporting_boxed_2413_ = lean_unbox(v_isExporting_2407_);
v_res_2414_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2406_, v_isExporting_boxed_2413_, v___x_2408_, v___y_2409_, v___x_2410_, v_a_x3f_2411_);
lean_dec(v_a_x3f_2411_);
lean_dec(v___y_2409_);
lean_dec(v___y_2406_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2415_, uint8_t v_isExporting_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v_env_2423_; lean_object* v___x_2424_; uint8_t v_isModule_2425_; 
v___x_2422_ = lean_st_ref_get(v___y_2420_);
v_env_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc_ref(v_env_2423_);
lean_dec(v___x_2422_);
v___x_2424_ = l_Lean_Environment_header(v_env_2423_);
v_isModule_2425_ = lean_ctor_get_uint8(v___x_2424_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2424_);
if (v_isModule_2425_ == 0)
{
lean_object* v___x_2426_; 
lean_dec_ref(v_env_2423_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
v___x_2426_ = lean_apply_5(v_x_2415_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, lean_box(0));
return v___x_2426_;
}
else
{
uint8_t v_isExporting_2427_; 
v_isExporting_2427_ = lean_ctor_get_uint8(v_env_2423_, sizeof(void*)*8);
lean_dec_ref(v_env_2423_);
if (v_isExporting_2416_ == 0)
{
if (v_isExporting_2427_ == 0)
{
lean_object* v___x_2493_; 
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
v___x_2493_ = lean_apply_5(v_x_2415_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, lean_box(0));
return v___x_2493_;
}
else
{
goto v___jp_2428_;
}
}
else
{
if (v_isExporting_2427_ == 0)
{
goto v___jp_2428_;
}
else
{
lean_object* v___x_2494_; 
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
v___x_2494_ = lean_apply_5(v_x_2415_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, lean_box(0));
return v___x_2494_;
}
}
v___jp_2428_:
{
lean_object* v___x_2429_; lean_object* v_env_2430_; lean_object* v_nextMacroScope_2431_; lean_object* v_ngen_2432_; lean_object* v_auxDeclNGen_2433_; lean_object* v_traceState_2434_; lean_object* v_messages_2435_; lean_object* v_infoState_2436_; lean_object* v_snapshotTasks_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2491_; 
v___x_2429_ = lean_st_ref_take(v___y_2420_);
v_env_2430_ = lean_ctor_get(v___x_2429_, 0);
v_nextMacroScope_2431_ = lean_ctor_get(v___x_2429_, 1);
v_ngen_2432_ = lean_ctor_get(v___x_2429_, 2);
v_auxDeclNGen_2433_ = lean_ctor_get(v___x_2429_, 3);
v_traceState_2434_ = lean_ctor_get(v___x_2429_, 4);
v_messages_2435_ = lean_ctor_get(v___x_2429_, 6);
v_infoState_2436_ = lean_ctor_get(v___x_2429_, 7);
v_snapshotTasks_2437_ = lean_ctor_get(v___x_2429_, 8);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2429_, 5);
lean_dec(v_unused_2492_);
v___x_2439_ = v___x_2429_;
v_isShared_2440_ = v_isSharedCheck_2491_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_snapshotTasks_2437_);
lean_inc(v_infoState_2436_);
lean_inc(v_messages_2435_);
lean_inc(v_traceState_2434_);
lean_inc(v_auxDeclNGen_2433_);
lean_inc(v_ngen_2432_);
lean_inc(v_nextMacroScope_2431_);
lean_inc(v_env_2430_);
lean_dec(v___x_2429_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2491_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2441_ = l_Lean_Environment_setExporting(v_env_2430_, v_isExporting_2416_);
v___x_2442_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 5, v___x_2442_);
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2444_ = v___x_2439_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_nextMacroScope_2431_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_ngen_2432_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_auxDeclNGen_2433_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v_traceState_2434_);
lean_ctor_set(v_reuseFailAlloc_2490_, 5, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2490_, 6, v_messages_2435_);
lean_ctor_set(v_reuseFailAlloc_2490_, 7, v_infoState_2436_);
lean_ctor_set(v_reuseFailAlloc_2490_, 8, v_snapshotTasks_2437_);
v___x_2444_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_mctx_2447_; lean_object* v_zetaDeltaFVarIds_2448_; lean_object* v_postponed_2449_; lean_object* v_diag_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2488_; 
v___x_2445_ = lean_st_ref_put(v___y_2420_, v___x_2444_);
v___x_2446_ = lean_st_ref_take(v___y_2418_);
v_mctx_2447_ = lean_ctor_get(v___x_2446_, 0);
v_zetaDeltaFVarIds_2448_ = lean_ctor_get(v___x_2446_, 2);
v_postponed_2449_ = lean_ctor_get(v___x_2446_, 3);
v_diag_2450_ = lean_ctor_get(v___x_2446_, 4);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; 
v_unused_2489_ = lean_ctor_get(v___x_2446_, 1);
lean_dec(v_unused_2489_);
v___x_2452_ = v___x_2446_;
v_isShared_2453_ = v_isSharedCheck_2488_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_diag_2450_);
lean_inc(v_postponed_2449_);
lean_inc(v_zetaDeltaFVarIds_2448_);
lean_inc(v_mctx_2447_);
lean_dec(v___x_2446_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2488_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2454_);
v___x_2456_ = v___x_2452_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_mctx_2447_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2487_, 2, v_zetaDeltaFVarIds_2448_);
lean_ctor_set(v_reuseFailAlloc_2487_, 3, v_postponed_2449_);
lean_ctor_set(v_reuseFailAlloc_2487_, 4, v_diag_2450_);
v___x_2456_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v_r_2458_; 
v___x_2457_ = lean_st_ref_put(v___y_2418_, v___x_2456_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
v_r_2458_ = lean_apply_5(v_x_2415_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, lean_box(0));
if (lean_obj_tag(v_r_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2475_; 
v_a_2459_ = lean_ctor_get(v_r_2458_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_r_2458_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2461_ = v_r_2458_;
v_isShared_2462_ = v_isSharedCheck_2475_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v_r_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2475_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
lean_inc(v_a_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set_tag(v___x_2461_, 1);
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
v___x_2465_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2420_, v_isExporting_2427_, v___x_2442_, v___y_2418_, v___x_2454_, v___x_2464_);
lean_dec_ref(v___x_2464_);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v___x_2465_, 0);
lean_dec(v_unused_2473_);
v___x_2467_ = v___x_2465_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_dec(v___x_2465_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v_a_2459_);
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2459_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
v_a_2476_ = lean_ctor_get(v_r_2458_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v_r_2458_, 1);
v___x_2477_ = lean_box(0);
v___x_2478_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2420_, v_isExporting_2427_, v___x_2442_, v___y_2418_, v___x_2454_, v___x_2477_);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v___x_2478_, 0);
lean_dec(v_unused_2486_);
v___x_2480_ = v___x_2478_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_dec(v___x_2478_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 1);
lean_ctor_set(v___x_2480_, 0, v_a_2476_);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2476_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2495_, lean_object* v_isExporting_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_isExporting_boxed_2502_; lean_object* v_res_2503_; 
v_isExporting_boxed_2502_ = lean_unbox(v_isExporting_2496_);
v_res_2503_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2495_, v_isExporting_boxed_2502_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2504_, uint8_t v_when_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
if (v_when_2505_ == 0)
{
lean_object* v___x_2511_; 
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
v___x_2511_ = lean_apply_5(v_x_2504_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, lean_box(0));
return v___x_2511_;
}
else
{
uint8_t v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = 0;
v___x_2513_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2504_, v___x_2512_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2514_, lean_object* v_when_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
uint8_t v_when_boxed_2521_; lean_object* v_res_2522_; 
v_when_boxed_2521_ = lean_unbox(v_when_2515_);
v_res_2522_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2514_, v_when_boxed_2521_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2522_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2525_ = l_Lean_stringToMessageData(v___x_2524_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2528_ = l_Lean_stringToMessageData(v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2532_, uint8_t v_nonRec_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; lean_object* v_env_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___f_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2539_ = lean_st_ref_get(v___y_2537_);
v_env_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc_ref(v_env_2540_);
lean_dec(v___x_2539_);
v___x_2541_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2532_);
v___x_2542_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2540_, v_declName_2532_, v___x_2541_);
v___x_2543_ = lean_box(v_nonRec_2533_);
lean_inc(v___x_2542_);
v___f_2544_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2544_, 0, v___x_2542_);
lean_closure_set(v___f_2544_, 1, v_declName_2532_);
lean_closure_set(v___f_2544_, 2, v___x_2543_);
lean_closure_set(v___f_2544_, 3, v___x_2541_);
v___x_2545_ = 1;
v___x_2546_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2544_, v___x_2545_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
if (lean_obj_tag(v_a_2547_) == 1)
{
lean_object* v_val_2548_; uint8_t v___x_2549_; 
v_val_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v_a_2547_, 1);
v___x_2549_ = lean_name_eq(v_val_2548_, v___x_2542_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec_ref_known(v___x_2546_, 1);
v___x_2550_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2551_ = l_Lean_MessageData_ofName(v_val_2548_);
v___x_2552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = l_Lean_MessageData_ofName(v___x_2542_);
v___x_2556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2558_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_dec(v_val_2548_);
lean_dec(v___x_2542_);
return v___x_2546_;
}
}
else
{
lean_dec(v_a_2547_);
lean_dec(v___x_2542_);
return v___x_2546_;
}
}
else
{
lean_dec(v___x_2542_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2568_, lean_object* v_nonRec_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
uint8_t v_nonRec_boxed_2575_; lean_object* v_res_2576_; 
v_nonRec_boxed_2575_ = lean_unbox(v_nonRec_2569_);
v_res_2576_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2568_, v_nonRec_boxed_2575_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2577_, uint8_t v_nonRec_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v___x_2584_; lean_object* v___f_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2584_ = lean_box(v_nonRec_2578_);
v___f_2585_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2585_, 0, v_declName_2577_);
lean_closure_set(v___f_2585_, 1, v___x_2584_);
v___x_2586_ = lean_unsigned_to_nat(32u);
v___x_2587_ = lean_mk_empty_array_with_capacity(v___x_2586_);
lean_dec_ref(v___x_2587_);
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2589_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2590_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2588_, v___x_2589_, v___f_2585_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2591_, lean_object* v_nonRec_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_){
_start:
{
uint8_t v_nonRec_boxed_2598_; lean_object* v_res_2599_; 
v_nonRec_boxed_2598_ = lean_unbox(v_nonRec_2592_);
v_res_2599_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2591_, v_nonRec_boxed_2598_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2600_, lean_object* v_as_2601_, lean_object* v_as_x27_2602_, lean_object* v_b_2603_, lean_object* v_a_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2600_, v_as_x27_2602_, v_b_2603_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2611_, lean_object* v_as_2612_, lean_object* v_as_x27_2613_, lean_object* v_b_2614_, lean_object* v_a_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2611_, v_as_2612_, v_as_x27_2613_, v_b_2614_, v_a_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v_as_x27_2613_);
lean_dec(v_as_2612_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2622_, lean_object* v_x_2623_, uint8_t v_isExporting_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2623_, v_isExporting_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2631_, lean_object* v_x_2632_, lean_object* v_isExporting_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
uint8_t v_isExporting_boxed_2639_; lean_object* v_res_2640_; 
v_isExporting_boxed_2639_ = lean_unbox(v_isExporting_2633_);
v_res_2640_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2631_, v_x_2632_, v_isExporting_boxed_2639_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2641_, lean_object* v_x_2642_, uint8_t v_when_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2642_, v_when_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2650_, lean_object* v_x_2651_, lean_object* v_when_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v_when_boxed_2658_; lean_object* v_res_2659_; 
v_when_boxed_2658_ = lean_unbox(v_when_2652_);
v_res_2659_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2650_, v_x_2651_, v_when_boxed_2658_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2660_, lean_object* v_msg_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2668_, lean_object* v_msg_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2668_, v_msg_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
return v_res_2675_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_unsigned_to_nat(32u);
v___x_2677_ = lean_mk_empty_array_with_capacity(v___x_2676_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2679_ = ((size_t)5ULL);
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = lean_unsigned_to_nat(32u);
v___x_2682_ = lean_mk_empty_array_with_capacity(v___x_2681_);
v___x_2683_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2684_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v___x_2682_);
lean_ctor_set(v___x_2684_, 2, v___x_2680_);
lean_ctor_set(v___x_2684_, 3, v___x_2680_);
lean_ctor_set_usize(v___x_2684_, 4, v___x_2679_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; lean_object* v_traceState_2688_; lean_object* v_traces_2689_; lean_object* v___x_2690_; lean_object* v_traceState_2691_; lean_object* v_env_2692_; lean_object* v_nextMacroScope_2693_; lean_object* v_ngen_2694_; lean_object* v_auxDeclNGen_2695_; lean_object* v_cache_2696_; lean_object* v_messages_2697_; lean_object* v_infoState_2698_; lean_object* v_snapshotTasks_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2718_; 
v___x_2687_ = lean_st_ref_get(v___y_2685_);
v_traceState_2688_ = lean_ctor_get(v___x_2687_, 4);
lean_inc_ref(v_traceState_2688_);
lean_dec(v___x_2687_);
v_traces_2689_ = lean_ctor_get(v_traceState_2688_, 0);
lean_inc_ref(v_traces_2689_);
lean_dec_ref(v_traceState_2688_);
v___x_2690_ = lean_st_ref_take(v___y_2685_);
v_traceState_2691_ = lean_ctor_get(v___x_2690_, 4);
v_env_2692_ = lean_ctor_get(v___x_2690_, 0);
v_nextMacroScope_2693_ = lean_ctor_get(v___x_2690_, 1);
v_ngen_2694_ = lean_ctor_get(v___x_2690_, 2);
v_auxDeclNGen_2695_ = lean_ctor_get(v___x_2690_, 3);
v_cache_2696_ = lean_ctor_get(v___x_2690_, 5);
v_messages_2697_ = lean_ctor_get(v___x_2690_, 6);
v_infoState_2698_ = lean_ctor_get(v___x_2690_, 7);
v_snapshotTasks_2699_ = lean_ctor_get(v___x_2690_, 8);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2701_ = v___x_2690_;
v_isShared_2702_ = v_isSharedCheck_2718_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_snapshotTasks_2699_);
lean_inc(v_infoState_2698_);
lean_inc(v_messages_2697_);
lean_inc(v_cache_2696_);
lean_inc(v_traceState_2691_);
lean_inc(v_auxDeclNGen_2695_);
lean_inc(v_ngen_2694_);
lean_inc(v_nextMacroScope_2693_);
lean_inc(v_env_2692_);
lean_dec(v___x_2690_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2718_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
uint64_t v_tid_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2716_; 
v_tid_2703_ = lean_ctor_get_uint64(v_traceState_2691_, sizeof(void*)*1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_traceState_2691_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; 
v_unused_2717_ = lean_ctor_get(v_traceState_2691_, 0);
lean_dec(v_unused_2717_);
v___x_2705_ = v_traceState_2691_;
v_isShared_2706_ = v_isSharedCheck_2716_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v_traceState_2691_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2716_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2707_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2707_);
v___x_2709_ = v___x_2705_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2707_);
lean_ctor_set_uint64(v_reuseFailAlloc_2715_, sizeof(void*)*1, v_tid_2703_);
v___x_2709_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2711_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 4, v___x_2709_);
v___x_2711_ = v___x_2701_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_env_2692_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_nextMacroScope_2693_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v_ngen_2694_);
lean_ctor_set(v_reuseFailAlloc_2714_, 3, v_auxDeclNGen_2695_);
lean_ctor_set(v_reuseFailAlloc_2714_, 4, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2714_, 5, v_cache_2696_);
lean_ctor_set(v_reuseFailAlloc_2714_, 6, v_messages_2697_);
lean_ctor_set(v_reuseFailAlloc_2714_, 7, v_infoState_2698_);
lean_ctor_set(v_reuseFailAlloc_2714_, 8, v_snapshotTasks_2699_);
v___x_2711_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = lean_st_ref_put(v___y_2685_, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2713_, 0, v_traces_2689_);
return v___x_2713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2719_);
lean_dec(v___y_2719_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
uint8_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = 0;
v___x_2735_ = lean_box(v___x_2734_);
v___x_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
return v_res_2741_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2744_ = l_Lean_stringToMessageData(v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2745_, lean_object* v_x_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2750_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2751_ = l_Lean_MessageData_ofName(v_name_2745_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2754_, lean_object* v_x_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2754_, v_x_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec_ref(v_x_2755_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2760_){
_start:
{
if (lean_obj_tag(v_x_2760_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_a_2762_ = lean_ctor_get(v_x_2760_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_x_2760_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v_x_2760_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v_x_2760_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 1);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
v_a_2770_ = lean_ctor_get(v_x_2760_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_x_2760_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v_x_2760_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v_x_2760_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 0);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2778_);
return v_res_2780_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2781_){
_start:
{
if (lean_obj_tag(v_e_2781_) == 0)
{
uint8_t v___x_2782_; 
v___x_2782_ = 2;
return v___x_2782_;
}
else
{
lean_object* v_a_2783_; uint8_t v___x_2784_; 
v_a_2783_ = lean_ctor_get(v_e_2781_, 0);
v___x_2784_ = lean_unbox(v_a_2783_);
if (v___x_2784_ == 0)
{
uint8_t v___x_2785_; 
v___x_2785_ = 1;
return v___x_2785_;
}
else
{
uint8_t v___x_2786_; 
v___x_2786_ = 0;
return v___x_2786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2787_){
_start:
{
uint8_t v_res_2788_; lean_object* v_r_2789_; 
v_res_2788_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2787_);
lean_dec_ref(v_e_2787_);
v_r_2789_ = lean_box(v_res_2788_);
return v_r_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2790_, size_t v_i_2791_, lean_object* v_bs_2792_){
_start:
{
uint8_t v___x_2793_; 
v___x_2793_ = lean_usize_dec_lt(v_i_2791_, v_sz_2790_);
if (v___x_2793_ == 0)
{
return v_bs_2792_;
}
else
{
lean_object* v_v_2794_; lean_object* v_msg_2795_; lean_object* v___x_2796_; lean_object* v_bs_x27_2797_; size_t v___x_2798_; size_t v___x_2799_; lean_object* v___x_2800_; 
v_v_2794_ = lean_array_uget_borrowed(v_bs_2792_, v_i_2791_);
v_msg_2795_ = lean_ctor_get(v_v_2794_, 1);
lean_inc_ref(v_msg_2795_);
v___x_2796_ = lean_unsigned_to_nat(0u);
v_bs_x27_2797_ = lean_array_uset(v_bs_2792_, v_i_2791_, v___x_2796_);
v___x_2798_ = ((size_t)1ULL);
v___x_2799_ = lean_usize_add(v_i_2791_, v___x_2798_);
v___x_2800_ = lean_array_uset(v_bs_x27_2797_, v_i_2791_, v_msg_2795_);
v_i_2791_ = v___x_2799_;
v_bs_2792_ = v___x_2800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2802_, lean_object* v_i_2803_, lean_object* v_bs_2804_){
_start:
{
size_t v_sz_boxed_2805_; size_t v_i_boxed_2806_; lean_object* v_res_2807_; 
v_sz_boxed_2805_ = lean_unbox_usize(v_sz_2802_);
lean_dec(v_sz_2802_);
v_i_boxed_2806_ = lean_unbox_usize(v_i_2803_);
lean_dec(v_i_2803_);
v_res_2807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2805_, v_i_boxed_2806_, v_bs_2804_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2808_, lean_object* v_data_2809_, lean_object* v_ref_2810_, lean_object* v_msg_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_toCold_2815_; lean_object* v_currRecDepth_2816_; lean_object* v_ref_2817_; uint8_t v_diag_2818_; uint8_t v_suppressElabErrors_2819_; lean_object* v___x_2820_; lean_object* v_traceState_2821_; lean_object* v_traces_2822_; lean_object* v_ref_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; size_t v_sz_2826_; size_t v___x_2827_; lean_object* v___x_2828_; lean_object* v_msg_2829_; lean_object* v___x_2830_; lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2868_; 
v_toCold_2815_ = lean_ctor_get(v___y_2812_, 0);
v_currRecDepth_2816_ = lean_ctor_get(v___y_2812_, 1);
v_ref_2817_ = lean_ctor_get(v___y_2812_, 2);
v_diag_2818_ = lean_ctor_get_uint8(v___y_2812_, sizeof(void*)*3);
v_suppressElabErrors_2819_ = lean_ctor_get_uint8(v___y_2812_, sizeof(void*)*3 + 1);
v___x_2820_ = lean_st_ref_get(v___y_2813_);
v_traceState_2821_ = lean_ctor_get(v___x_2820_, 4);
lean_inc_ref(v_traceState_2821_);
lean_dec(v___x_2820_);
v_traces_2822_ = lean_ctor_get(v_traceState_2821_, 0);
lean_inc_ref(v_traces_2822_);
lean_dec_ref(v_traceState_2821_);
v_ref_2823_ = l_Lean_replaceRef(v_ref_2810_, v_ref_2817_);
lean_inc(v_currRecDepth_2816_);
lean_inc_ref(v_toCold_2815_);
v___x_2824_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2824_, 0, v_toCold_2815_);
lean_ctor_set(v___x_2824_, 1, v_currRecDepth_2816_);
lean_ctor_set(v___x_2824_, 2, v_ref_2823_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*3, v_diag_2818_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*3 + 1, v_suppressElabErrors_2819_);
v___x_2825_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2822_);
lean_dec_ref(v_traces_2822_);
v_sz_2826_ = lean_array_size(v___x_2825_);
v___x_2827_ = ((size_t)0ULL);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2826_, v___x_2827_, v___x_2825_);
v_msg_2829_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2829_, 0, v_data_2809_);
lean_ctor_set(v_msg_2829_, 1, v_msg_2811_);
lean_ctor_set(v_msg_2829_, 2, v___x_2828_);
v___x_2830_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2829_, v___x_2824_, v___y_2813_);
lean_dec_ref_known(v___x_2824_, 3);
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_2868_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2868_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v_traceState_2836_; lean_object* v_env_2837_; lean_object* v_nextMacroScope_2838_; lean_object* v_ngen_2839_; lean_object* v_auxDeclNGen_2840_; lean_object* v_cache_2841_; lean_object* v_messages_2842_; lean_object* v_infoState_2843_; lean_object* v_snapshotTasks_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2867_; 
v___x_2835_ = lean_st_ref_take(v___y_2813_);
v_traceState_2836_ = lean_ctor_get(v___x_2835_, 4);
v_env_2837_ = lean_ctor_get(v___x_2835_, 0);
v_nextMacroScope_2838_ = lean_ctor_get(v___x_2835_, 1);
v_ngen_2839_ = lean_ctor_get(v___x_2835_, 2);
v_auxDeclNGen_2840_ = lean_ctor_get(v___x_2835_, 3);
v_cache_2841_ = lean_ctor_get(v___x_2835_, 5);
v_messages_2842_ = lean_ctor_get(v___x_2835_, 6);
v_infoState_2843_ = lean_ctor_get(v___x_2835_, 7);
v_snapshotTasks_2844_ = lean_ctor_get(v___x_2835_, 8);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2846_ = v___x_2835_;
v_isShared_2847_ = v_isSharedCheck_2867_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_snapshotTasks_2844_);
lean_inc(v_infoState_2843_);
lean_inc(v_messages_2842_);
lean_inc(v_cache_2841_);
lean_inc(v_traceState_2836_);
lean_inc(v_auxDeclNGen_2840_);
lean_inc(v_ngen_2839_);
lean_inc(v_nextMacroScope_2838_);
lean_inc(v_env_2837_);
lean_dec(v___x_2835_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2867_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
uint64_t v_tid_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2865_; 
v_tid_2848_ = lean_ctor_get_uint64(v_traceState_2836_, sizeof(void*)*1);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_traceState_2836_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; 
v_unused_2866_ = lean_ctor_get(v_traceState_2836_, 0);
lean_dec(v_unused_2866_);
v___x_2850_ = v_traceState_2836_;
v_isShared_2851_ = v_isSharedCheck_2865_;
goto v_resetjp_2849_;
}
else
{
lean_dec(v_traceState_2836_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2865_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v_ref_2810_);
lean_ctor_set(v___x_2852_, 1, v_a_2831_);
v___x_2853_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2808_, v___x_2852_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2853_);
v___x_2855_ = v___x_2850_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2853_);
lean_ctor_set_uint64(v_reuseFailAlloc_2864_, sizeof(void*)*1, v_tid_2848_);
v___x_2855_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2857_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 4, v___x_2855_);
v___x_2857_ = v___x_2846_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_env_2837_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_nextMacroScope_2838_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_ngen_2839_);
lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_auxDeclNGen_2840_);
lean_ctor_set(v_reuseFailAlloc_2863_, 4, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2863_, 5, v_cache_2841_);
lean_ctor_set(v_reuseFailAlloc_2863_, 6, v_messages_2842_);
lean_ctor_set(v_reuseFailAlloc_2863_, 7, v_infoState_2843_);
lean_ctor_set(v_reuseFailAlloc_2863_, 8, v_snapshotTasks_2844_);
v___x_2857_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2858_ = lean_st_ref_put(v___y_2813_, v___x_2857_);
v___x_2859_ = lean_box(0);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2859_);
v___x_2861_ = v___x_2833_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2869_, lean_object* v_data_2870_, lean_object* v_ref_2871_, lean_object* v_msg_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2869_, v_data_2870_, v_ref_2871_, v_msg_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
return v_res_2876_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2879_ = l_Lean_stringToMessageData(v___x_2878_);
return v___x_2879_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2880_; double v___x_2881_; 
v___x_2880_ = lean_unsigned_to_nat(1000u);
v___x_2881_ = lean_float_of_nat(v___x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2882_, uint8_t v_collapsed_2883_, lean_object* v_tag_2884_, lean_object* v_opts_2885_, uint8_t v_clsEnabled_2886_, lean_object* v_oldTraces_2887_, lean_object* v_msg_2888_, lean_object* v_resStartStop_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_fst_2893_; lean_object* v_snd_2894_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v_data_2898_; lean_object* v_fst_2909_; lean_object* v_snd_2910_; lean_object* v___x_2911_; uint8_t v___x_2912_; lean_object* v___y_2914_; lean_object* v_a_2915_; uint8_t v___y_2930_; double v___y_2961_; 
v_fst_2893_ = lean_ctor_get(v_resStartStop_2889_, 0);
lean_inc(v_fst_2893_);
v_snd_2894_ = lean_ctor_get(v_resStartStop_2889_, 1);
lean_inc(v_snd_2894_);
lean_dec_ref(v_resStartStop_2889_);
v_fst_2909_ = lean_ctor_get(v_snd_2894_, 0);
lean_inc(v_fst_2909_);
v_snd_2910_ = lean_ctor_get(v_snd_2894_, 1);
lean_inc(v_snd_2910_);
lean_dec(v_snd_2894_);
v___x_2911_ = l_Lean_trace_profiler;
v___x_2912_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2885_, v___x_2911_);
if (v___x_2912_ == 0)
{
v___y_2930_ = v___x_2912_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2967_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2885_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; double v___x_2970_; double v___x_2971_; double v___x_2972_; 
v___x_2968_ = l_Lean_trace_profiler_threshold;
v___x_2969_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2885_, v___x_2968_);
v___x_2970_ = lean_float_of_nat(v___x_2969_);
v___x_2971_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_2972_ = lean_float_div(v___x_2970_, v___x_2971_);
v___y_2961_ = v___x_2972_;
goto v___jp_2960_;
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; double v___x_2975_; 
v___x_2973_ = l_Lean_trace_profiler_threshold;
v___x_2974_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2885_, v___x_2973_);
v___x_2975_ = lean_float_of_nat(v___x_2974_);
v___y_2961_ = v___x_2975_;
goto v___jp_2960_;
}
}
v___jp_2895_:
{
lean_object* v___x_2899_; 
lean_inc(v___y_2897_);
v___x_2899_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2887_, v_data_2898_, v___y_2897_, v___y_2896_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v___x_2900_; 
lean_dec_ref_known(v___x_2899_, 1);
v___x_2900_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2893_);
return v___x_2900_;
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v_fst_2893_);
v_a_2901_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2899_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2899_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
v___jp_2913_:
{
uint8_t v_result_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; double v___x_2919_; lean_object* v_data_2920_; 
v_result_2916_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2893_);
v___x_2917_ = lean_box(v_result_2916_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
v___x_2919_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2884_);
lean_inc_ref(v___x_2918_);
lean_inc(v_cls_2882_);
v_data_2920_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2920_, 0, v_cls_2882_);
lean_ctor_set(v_data_2920_, 1, v___x_2918_);
lean_ctor_set(v_data_2920_, 2, v_tag_2884_);
lean_ctor_set_float(v_data_2920_, sizeof(void*)*3, v___x_2919_);
lean_ctor_set_float(v_data_2920_, sizeof(void*)*3 + 8, v___x_2919_);
lean_ctor_set_uint8(v_data_2920_, sizeof(void*)*3 + 16, v_collapsed_2883_);
if (v___x_2912_ == 0)
{
lean_dec_ref_known(v___x_2918_, 1);
lean_dec(v_snd_2910_);
lean_dec(v_fst_2909_);
lean_dec_ref(v_tag_2884_);
lean_dec(v_cls_2882_);
v___y_2896_ = v_a_2915_;
v___y_2897_ = v___y_2914_;
v_data_2898_ = v_data_2920_;
goto v___jp_2895_;
}
else
{
lean_object* v_data_2921_; double v___x_2922_; double v___x_2923_; 
lean_dec_ref_known(v_data_2920_, 3);
v_data_2921_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2921_, 0, v_cls_2882_);
lean_ctor_set(v_data_2921_, 1, v___x_2918_);
lean_ctor_set(v_data_2921_, 2, v_tag_2884_);
v___x_2922_ = lean_unbox_float(v_fst_2909_);
lean_dec(v_fst_2909_);
lean_ctor_set_float(v_data_2921_, sizeof(void*)*3, v___x_2922_);
v___x_2923_ = lean_unbox_float(v_snd_2910_);
lean_dec(v_snd_2910_);
lean_ctor_set_float(v_data_2921_, sizeof(void*)*3 + 8, v___x_2923_);
lean_ctor_set_uint8(v_data_2921_, sizeof(void*)*3 + 16, v_collapsed_2883_);
v___y_2896_ = v_a_2915_;
v___y_2897_ = v___y_2914_;
v_data_2898_ = v_data_2921_;
goto v___jp_2895_;
}
}
v___jp_2924_:
{
lean_object* v_ref_2925_; lean_object* v___x_2926_; 
v_ref_2925_ = lean_ctor_get(v___y_2890_, 2);
lean_inc(v___y_2891_);
lean_inc_ref(v___y_2890_);
lean_inc(v_fst_2893_);
v___x_2926_ = lean_apply_4(v_msg_2888_, v_fst_2893_, v___y_2890_, v___y_2891_, lean_box(0));
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___y_2914_ = v_ref_2925_;
v_a_2915_ = v_a_2927_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_2928_; 
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2914_ = v_ref_2925_;
v_a_2915_ = v___x_2928_;
goto v___jp_2913_;
}
}
v___jp_2929_:
{
if (v_clsEnabled_2886_ == 0)
{
if (v___y_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v_traceState_2932_; lean_object* v_env_2933_; lean_object* v_nextMacroScope_2934_; lean_object* v_ngen_2935_; lean_object* v_auxDeclNGen_2936_; lean_object* v_cache_2937_; lean_object* v_messages_2938_; lean_object* v_infoState_2939_; lean_object* v_snapshotTasks_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v_snd_2910_);
lean_dec(v_fst_2909_);
lean_dec_ref(v_msg_2888_);
lean_dec_ref(v_tag_2884_);
lean_dec(v_cls_2882_);
v___x_2931_ = lean_st_ref_take(v___y_2891_);
v_traceState_2932_ = lean_ctor_get(v___x_2931_, 4);
v_env_2933_ = lean_ctor_get(v___x_2931_, 0);
v_nextMacroScope_2934_ = lean_ctor_get(v___x_2931_, 1);
v_ngen_2935_ = lean_ctor_get(v___x_2931_, 2);
v_auxDeclNGen_2936_ = lean_ctor_get(v___x_2931_, 3);
v_cache_2937_ = lean_ctor_get(v___x_2931_, 5);
v_messages_2938_ = lean_ctor_get(v___x_2931_, 6);
v_infoState_2939_ = lean_ctor_get(v___x_2931_, 7);
v_snapshotTasks_2940_ = lean_ctor_get(v___x_2931_, 8);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2942_ = v___x_2931_;
v_isShared_2943_ = v_isSharedCheck_2959_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snapshotTasks_2940_);
lean_inc(v_infoState_2939_);
lean_inc(v_messages_2938_);
lean_inc(v_cache_2937_);
lean_inc(v_traceState_2932_);
lean_inc(v_auxDeclNGen_2936_);
lean_inc(v_ngen_2935_);
lean_inc(v_nextMacroScope_2934_);
lean_inc(v_env_2933_);
lean_dec(v___x_2931_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2959_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
uint64_t v_tid_2944_; lean_object* v_traces_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2958_; 
v_tid_2944_ = lean_ctor_get_uint64(v_traceState_2932_, sizeof(void*)*1);
v_traces_2945_ = lean_ctor_get(v_traceState_2932_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_traceState_2932_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2947_ = v_traceState_2932_;
v_isShared_2948_ = v_isSharedCheck_2958_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_traces_2945_);
lean_dec(v_traceState_2932_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2958_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2887_, v_traces_2945_);
lean_dec_ref(v_traces_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2949_);
lean_ctor_set_uint64(v_reuseFailAlloc_2957_, sizeof(void*)*1, v_tid_2944_);
v___x_2951_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 4, v___x_2951_);
v___x_2953_ = v___x_2942_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_env_2933_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_nextMacroScope_2934_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_ngen_2935_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_auxDeclNGen_2936_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2956_, 5, v_cache_2937_);
lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_messages_2938_);
lean_ctor_set(v_reuseFailAlloc_2956_, 7, v_infoState_2939_);
lean_ctor_set(v_reuseFailAlloc_2956_, 8, v_snapshotTasks_2940_);
v___x_2953_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_st_ref_put(v___y_2891_, v___x_2953_);
v___x_2955_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2893_);
return v___x_2955_;
}
}
}
}
}
else
{
goto v___jp_2924_;
}
}
else
{
goto v___jp_2924_;
}
}
v___jp_2960_:
{
double v___x_2962_; double v___x_2963_; double v___x_2964_; uint8_t v___x_2965_; 
v___x_2962_ = lean_unbox_float(v_snd_2910_);
v___x_2963_ = lean_unbox_float(v_fst_2909_);
v___x_2964_ = lean_float_sub(v___x_2962_, v___x_2963_);
v___x_2965_ = lean_float_decLt(v___y_2961_, v___x_2964_);
v___y_2930_ = v___x_2965_;
goto v___jp_2929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_2976_, lean_object* v_collapsed_2977_, lean_object* v_tag_2978_, lean_object* v_opts_2979_, lean_object* v_clsEnabled_2980_, lean_object* v_oldTraces_2981_, lean_object* v_msg_2982_, lean_object* v_resStartStop_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v_collapsed_boxed_2987_; uint8_t v_clsEnabled_boxed_2988_; lean_object* v_res_2989_; 
v_collapsed_boxed_2987_ = lean_unbox(v_collapsed_2977_);
v_clsEnabled_boxed_2988_ = lean_unbox(v_clsEnabled_2980_);
v_res_2989_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_2976_, v_collapsed_boxed_2987_, v_tag_2978_, v_opts_2979_, v_clsEnabled_boxed_2988_, v_oldTraces_2981_, v_msg_2982_, v_resStartStop_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec_ref(v_opts_2979_);
return v_res_2989_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
lean_ctor_set(v___x_2994_, 2, v___x_2993_);
lean_ctor_set(v___x_2994_, 3, v___x_2993_);
lean_ctor_set(v___x_2994_, 4, v___x_2992_);
lean_ctor_set(v___x_2994_, 5, v___x_2992_);
lean_ctor_set(v___x_2994_, 6, v___x_2992_);
lean_ctor_set(v___x_2994_, 7, v___x_2992_);
lean_ctor_set(v___x_2994_, 8, v___x_2992_);
lean_ctor_set(v___x_2994_, 9, v___x_2992_);
lean_ctor_set(v___x_2994_, 10, v___x_2992_);
return v___x_2994_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2996_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
lean_ctor_set(v___x_2996_, 2, v___x_2995_);
lean_ctor_set(v___x_2996_, 3, v___x_2995_);
lean_ctor_set(v___x_2996_, 4, v___x_2995_);
lean_ctor_set(v___x_2996_, 5, v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
lean_ctor_set(v___x_2998_, 2, v___x_2997_);
lean_ctor_set(v___x_2998_, 3, v___x_2997_);
lean_ctor_set(v___x_2998_, 4, v___x_2997_);
return v___x_2998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3004_ = l_Lean_Name_append(v___x_3003_, v___x_3002_);
return v___x_3004_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3005_; double v___x_3006_; 
v___x_3005_ = lean_unsigned_to_nat(1000000000u);
v___x_3006_ = lean_float_of_nat(v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3007_, lean_object* v___f_3008_, lean_object* v_name_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_toCold_3013_; lean_object* v_options_3014_; uint8_t v_hasTrace_3015_; 
v_toCold_3013_ = lean_ctor_get(v___y_3010_, 0);
v_options_3014_ = lean_ctor_get(v_toCold_3013_, 2);
v_hasTrace_3015_ = lean_ctor_get_uint8(v_options_3014_, sizeof(void*)*1);
if (v_hasTrace_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v_env_3017_; lean_object* v___x_3018_; 
lean_dec_ref(v___f_3008_);
v___x_3016_ = lean_st_ref_get(v___y_3011_);
v_env_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc_ref(v_env_3017_);
lean_dec(v___x_3016_);
lean_inc(v_name_3009_);
v___x_3018_ = l_Lean_Meta_declFromEqLikeName(v_env_3017_, v_name_3009_);
if (lean_obj_tag(v___x_3018_) == 1)
{
lean_object* v_val_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3124_; 
v_val_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3124_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_val_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3124_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_fst_3023_; lean_object* v_snd_3024_; lean_object* v___x_3025_; lean_object* v_env_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_fst_3023_ = lean_ctor_get(v_val_3019_, 0);
lean_inc_n(v_fst_3023_, 2);
v_snd_3024_ = lean_ctor_get(v_val_3019_, 1);
lean_inc_n(v_snd_3024_, 2);
lean_dec(v_val_3019_);
v___x_3025_ = lean_st_ref_get(v___y_3011_);
v_env_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc_ref(v_env_3026_);
lean_dec(v___x_3025_);
v___x_3027_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3026_, v_fst_3023_, v_snd_3024_);
v___x_3028_ = lean_name_eq(v_name_3009_, v___x_3027_);
lean_dec(v___x_3027_);
lean_dec(v_name_3009_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
lean_dec(v_snd_3024_);
lean_dec(v_fst_3023_);
lean_dec(v___x_3007_);
v___x_3029_ = lean_box(v_hasTrace_3015_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set_tag(v___x_3021_, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3029_);
v___x_3031_ = v___x_3021_;
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
uint8_t v___x_3033_; lean_object* v_a_3035_; 
lean_inc(v_snd_3024_);
v___x_3033_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3024_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3049_; uint8_t v___x_3050_; lean_object* v_a_3052_; 
lean_del_object(v___x_3021_);
v___x_3049_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3050_ = lean_string_dec_eq(v_snd_3024_, v___x_3049_);
lean_dec(v_snd_3024_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec(v_fst_3023_);
lean_dec(v___x_3007_);
v___x_3064_ = lean_box(v_hasTrace_3015_);
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
else
{
uint8_t v___x_3066_; uint8_t v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3069_; uint64_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3066_ = 1;
v___x_3067_ = 0;
v___x_3068_ = 2;
v___x_3069_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3069_, 0, v___x_3033_);
lean_ctor_set_uint8(v___x_3069_, 1, v___x_3033_);
lean_ctor_set_uint8(v___x_3069_, 2, v___x_3033_);
lean_ctor_set_uint8(v___x_3069_, 3, v___x_3033_);
lean_ctor_set_uint8(v___x_3069_, 4, v___x_3033_);
lean_ctor_set_uint8(v___x_3069_, 5, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 6, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 7, v___x_3033_);
lean_ctor_set_uint8(v___x_3069_, 8, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 9, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, 10, v___x_3067_);
lean_ctor_set_uint8(v___x_3069_, 11, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 12, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 13, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 14, v___x_3068_);
lean_ctor_set_uint8(v___x_3069_, 15, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 16, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 17, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 18, v___x_3050_);
lean_ctor_set_uint8(v___x_3069_, 19, v___x_3033_);
v___x_3070_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set_uint64(v___x_3071_, sizeof(void*)*1, v___x_3070_);
v___x_3072_ = lean_unsigned_to_nat(0u);
v___x_3073_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3074_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3075_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3076_ = lean_box(0);
lean_inc(v___x_3007_);
v___x_3077_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3077_, 0, v___x_3071_);
lean_ctor_set(v___x_3077_, 1, v___x_3007_);
lean_ctor_set(v___x_3077_, 2, v___x_3074_);
lean_ctor_set(v___x_3077_, 3, v___x_3075_);
lean_ctor_set(v___x_3077_, 4, v___x_3076_);
lean_ctor_set(v___x_3077_, 5, v___x_3072_);
lean_ctor_set(v___x_3077_, 6, v___x_3076_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*7, v___x_3033_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*7 + 1, v___x_3033_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*7 + 2, v___x_3033_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*7 + 3, v___x_3028_);
v___x_3078_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3079_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3080_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3078_);
lean_ctor_set(v___x_3081_, 1, v___x_3079_);
lean_ctor_set(v___x_3081_, 2, v___x_3007_);
lean_ctor_set(v___x_3081_, 3, v___x_3073_);
lean_ctor_set(v___x_3081_, 4, v___x_3080_);
v___x_3082_ = lean_st_mk_ref(v___x_3081_);
v___x_3083_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3023_, v___x_3028_, v___x_3077_, v___x_3082_, v___y_3010_, v___y_3011_);
lean_dec_ref_known(v___x_3077_, 7);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3085_ = lean_st_ref_get(v___x_3082_);
lean_dec(v___x_3082_);
lean_dec(v___x_3085_);
v_a_3052_ = v_a_3084_;
goto v___jp_3051_;
}
else
{
lean_dec(v___x_3082_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3086_; 
v_a_3086_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3083_, 1);
v_a_3052_ = v_a_3086_;
goto v___jp_3051_;
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
v_a_3087_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3083_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3083_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
v___jp_3051_:
{
if (lean_obj_tag(v_a_3052_) == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_box(v___x_3033_);
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
v___x_3058_ = lean_box(v___x_3050_);
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
}
else
{
uint8_t v___x_3095_; uint8_t v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; uint64_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec(v_snd_3024_);
v___x_3095_ = 1;
v___x_3096_ = 0;
v___x_3097_ = 2;
v___x_3098_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3098_, 0, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3098_, 1, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3098_, 2, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3098_, 3, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3098_, 4, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3098_, 5, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 6, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 7, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3098_, 8, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 9, v___x_3095_);
lean_ctor_set_uint8(v___x_3098_, 10, v___x_3096_);
lean_ctor_set_uint8(v___x_3098_, 11, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 12, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 13, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 14, v___x_3097_);
lean_ctor_set_uint8(v___x_3098_, 15, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 16, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 17, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 18, v___x_3033_);
lean_ctor_set_uint8(v___x_3098_, 19, v_hasTrace_3015_);
v___x_3099_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3098_);
v___x_3100_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set_uint64(v___x_3100_, sizeof(void*)*1, v___x_3099_);
v___x_3101_ = lean_unsigned_to_nat(0u);
v___x_3102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3103_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3104_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3105_ = lean_box(0);
lean_inc(v___x_3007_);
v___x_3106_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3106_, 0, v___x_3100_);
lean_ctor_set(v___x_3106_, 1, v___x_3007_);
lean_ctor_set(v___x_3106_, 2, v___x_3103_);
lean_ctor_set(v___x_3106_, 3, v___x_3104_);
lean_ctor_set(v___x_3106_, 4, v___x_3105_);
lean_ctor_set(v___x_3106_, 5, v___x_3101_);
lean_ctor_set(v___x_3106_, 6, v___x_3105_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*7, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*7 + 1, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*7 + 2, v_hasTrace_3015_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*7 + 3, v___x_3028_);
v___x_3107_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3108_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3109_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3107_);
lean_ctor_set(v___x_3110_, 1, v___x_3108_);
lean_ctor_set(v___x_3110_, 2, v___x_3007_);
lean_ctor_set(v___x_3110_, 3, v___x_3102_);
lean_ctor_set(v___x_3110_, 4, v___x_3109_);
v___x_3111_ = lean_st_mk_ref(v___x_3110_);
v___x_3112_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3023_, v___x_3106_, v___x_3111_, v___y_3010_, v___y_3011_);
lean_dec_ref_known(v___x_3106_, 7);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3114_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3114_ = lean_st_ref_get(v___x_3111_);
lean_dec(v___x_3111_);
lean_dec(v___x_3114_);
v_a_3035_ = v_a_3113_;
goto v___jp_3034_;
}
else
{
lean_dec(v___x_3111_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3115_; 
v_a_3115_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3112_, 1);
v_a_3035_ = v_a_3115_;
goto v___jp_3034_;
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_del_object(v___x_3021_);
v_a_3116_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3112_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3112_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
v___jp_3034_:
{
if (lean_obj_tag(v_a_3035_) == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3036_ = lean_box(v_hasTrace_3015_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set_tag(v___x_3021_, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3036_);
v___x_3038_ = v___x_3021_;
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
else
{
lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3047_; 
lean_del_object(v___x_3021_);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_a_3035_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v_a_3035_, 0);
lean_dec(v_unused_3048_);
v___x_3041_ = v_a_3035_;
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
else
{
lean_dec(v_a_3035_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3043_ = lean_box(v___x_3033_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3043_);
v___x_3045_ = v___x_3041_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec(v___x_3018_);
lean_dec(v_name_3009_);
lean_dec(v___x_3007_);
v___x_3125_ = lean_box(v_hasTrace_3015_);
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3127_; lean_object* v___f_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v_a_3136_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v_a_3151_; lean_object* v___y_3154_; lean_object* v___y_3155_; uint8_t v_a_3156_; uint8_t v___y_3160_; uint8_t v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v_a_3164_; uint8_t v___y_3166_; uint8_t v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v_a_3170_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v_a_3174_; lean_object* v___y_3184_; lean_object* v___y_3185_; uint8_t v_a_3186_; uint8_t v___y_3190_; lean_object* v___y_3191_; uint8_t v___y_3192_; lean_object* v___y_3193_; lean_object* v_a_3194_; uint8_t v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v_a_3199_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v_a_3204_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; 
v_inheritedTraceOptions_3127_ = lean_ctor_get(v_toCold_3013_, 11);
lean_inc(v_name_3009_);
v___f_3128_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3128_, 0, v_name_3009_);
v___x_3129_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3130_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3131_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3132_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3127_, v_options_3014_, v___x_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3341_ = l_Lean_trace_profiler;
v___x_3342_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3014_, v___x_3341_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; lean_object* v_env_3344_; lean_object* v___x_3345_; 
lean_dec_ref(v___f_3128_);
lean_dec_ref(v___f_3008_);
v___x_3343_ = lean_st_ref_get(v___y_3011_);
v_env_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc_ref(v_env_3344_);
lean_dec(v___x_3343_);
lean_inc(v_name_3009_);
v___x_3345_ = l_Lean_Meta_declFromEqLikeName(v_env_3344_, v_name_3009_);
if (lean_obj_tag(v___x_3345_) == 1)
{
lean_object* v_val_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3451_; 
v_val_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3451_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_val_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3451_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v___x_3352_; lean_object* v_env_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v_fst_3350_ = lean_ctor_get(v_val_3346_, 0);
lean_inc_n(v_fst_3350_, 2);
v_snd_3351_ = lean_ctor_get(v_val_3346_, 1);
lean_inc_n(v_snd_3351_, 2);
lean_dec(v_val_3346_);
v___x_3352_ = lean_st_ref_get(v___y_3011_);
v_env_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_ref(v_env_3353_);
lean_dec(v___x_3352_);
v___x_3354_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3353_, v_fst_3350_, v_snd_3351_);
v___x_3355_ = lean_name_eq(v_name_3009_, v___x_3354_);
lean_dec(v___x_3354_);
lean_dec(v_name_3009_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
lean_dec(v_snd_3351_);
lean_dec(v_fst_3350_);
lean_dec(v___x_3007_);
v___x_3356_ = lean_box(v___x_3342_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set_tag(v___x_3348_, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3356_);
v___x_3358_ = v___x_3348_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
else
{
uint8_t v___x_3360_; lean_object* v_a_3362_; 
lean_inc(v_snd_3351_);
v___x_3360_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3351_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3376_; uint8_t v___x_3377_; lean_object* v_a_3379_; 
lean_del_object(v___x_3348_);
v___x_3376_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3377_ = lean_string_dec_eq(v_snd_3351_, v___x_3376_);
lean_dec(v_snd_3351_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_dec(v_fst_3350_);
lean_dec(v___x_3007_);
v___x_3391_ = lean_box(v___x_3342_);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
else
{
uint8_t v___x_3393_; uint8_t v___x_3394_; uint8_t v___x_3395_; lean_object* v___x_3396_; uint64_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3393_ = 1;
v___x_3394_ = 0;
v___x_3395_ = 2;
v___x_3396_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3396_, 0, v___x_3360_);
lean_ctor_set_uint8(v___x_3396_, 1, v___x_3360_);
lean_ctor_set_uint8(v___x_3396_, 2, v___x_3360_);
lean_ctor_set_uint8(v___x_3396_, 3, v___x_3360_);
lean_ctor_set_uint8(v___x_3396_, 4, v___x_3360_);
lean_ctor_set_uint8(v___x_3396_, 5, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 6, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 7, v___x_3360_);
lean_ctor_set_uint8(v___x_3396_, 8, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 9, v___x_3393_);
lean_ctor_set_uint8(v___x_3396_, 10, v___x_3394_);
lean_ctor_set_uint8(v___x_3396_, 11, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 12, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 13, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 14, v___x_3395_);
lean_ctor_set_uint8(v___x_3396_, 15, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 16, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 17, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 18, v___x_3377_);
lean_ctor_set_uint8(v___x_3396_, 19, v___x_3360_);
v___x_3397_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3396_);
v___x_3398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set_uint64(v___x_3398_, sizeof(void*)*1, v___x_3397_);
v___x_3399_ = lean_unsigned_to_nat(0u);
v___x_3400_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3401_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3402_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3403_ = lean_box(0);
lean_inc(v___x_3007_);
v___x_3404_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3404_, 0, v___x_3398_);
lean_ctor_set(v___x_3404_, 1, v___x_3007_);
lean_ctor_set(v___x_3404_, 2, v___x_3401_);
lean_ctor_set(v___x_3404_, 3, v___x_3402_);
lean_ctor_set(v___x_3404_, 4, v___x_3403_);
lean_ctor_set(v___x_3404_, 5, v___x_3399_);
lean_ctor_set(v___x_3404_, 6, v___x_3403_);
lean_ctor_set_uint8(v___x_3404_, sizeof(void*)*7, v___x_3360_);
lean_ctor_set_uint8(v___x_3404_, sizeof(void*)*7 + 1, v___x_3360_);
lean_ctor_set_uint8(v___x_3404_, sizeof(void*)*7 + 2, v___x_3360_);
lean_ctor_set_uint8(v___x_3404_, sizeof(void*)*7 + 3, v_hasTrace_3015_);
v___x_3405_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3407_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3405_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
lean_ctor_set(v___x_3408_, 2, v___x_3007_);
lean_ctor_set(v___x_3408_, 3, v___x_3400_);
lean_ctor_set(v___x_3408_, 4, v___x_3407_);
v___x_3409_ = lean_st_mk_ref(v___x_3408_);
v___x_3410_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3350_, v_hasTrace_3015_, v___x_3404_, v___x_3409_, v___y_3010_, v___y_3011_);
lean_dec_ref_known(v___x_3404_, 7);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3412_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = lean_st_ref_get(v___x_3409_);
lean_dec(v___x_3409_);
lean_dec(v___x_3412_);
v_a_3379_ = v_a_3411_;
goto v___jp_3378_;
}
else
{
lean_dec(v___x_3409_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3413_; 
v_a_3413_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3410_, 1);
v_a_3379_ = v_a_3413_;
goto v___jp_3378_;
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
v_a_3414_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3410_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3410_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
v___jp_3378_:
{
if (lean_obj_tag(v_a_3379_) == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = lean_box(v___x_3360_);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
return v___x_3381_;
}
else
{
lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3389_; 
v_isSharedCheck_3389_ = !lean_is_exclusive(v_a_3379_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; 
v_unused_3390_ = lean_ctor_get(v_a_3379_, 0);
lean_dec(v_unused_3390_);
v___x_3383_ = v_a_3379_;
v_isShared_3384_ = v_isSharedCheck_3389_;
goto v_resetjp_3382_;
}
else
{
lean_dec(v_a_3379_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3389_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3385_ = lean_box(v___x_3377_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set_tag(v___x_3383_, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3385_);
v___x_3387_ = v___x_3383_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
else
{
uint8_t v___x_3422_; uint8_t v___x_3423_; uint8_t v___x_3424_; lean_object* v___x_3425_; uint64_t v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_dec(v_snd_3351_);
v___x_3422_ = 1;
v___x_3423_ = 0;
v___x_3424_ = 2;
v___x_3425_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3425_, 0, v___x_3342_);
lean_ctor_set_uint8(v___x_3425_, 1, v___x_3342_);
lean_ctor_set_uint8(v___x_3425_, 2, v___x_3342_);
lean_ctor_set_uint8(v___x_3425_, 3, v___x_3342_);
lean_ctor_set_uint8(v___x_3425_, 4, v___x_3342_);
lean_ctor_set_uint8(v___x_3425_, 5, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 6, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 7, v___x_3342_);
lean_ctor_set_uint8(v___x_3425_, 8, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 9, v___x_3422_);
lean_ctor_set_uint8(v___x_3425_, 10, v___x_3423_);
lean_ctor_set_uint8(v___x_3425_, 11, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 12, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 13, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 14, v___x_3424_);
lean_ctor_set_uint8(v___x_3425_, 15, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 16, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 17, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 18, v___x_3360_);
lean_ctor_set_uint8(v___x_3425_, 19, v___x_3342_);
v___x_3426_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3425_);
v___x_3427_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set_uint64(v___x_3427_, sizeof(void*)*1, v___x_3426_);
v___x_3428_ = lean_unsigned_to_nat(0u);
v___x_3429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3430_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3431_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3432_ = lean_box(0);
lean_inc(v___x_3007_);
v___x_3433_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3433_, 0, v___x_3427_);
lean_ctor_set(v___x_3433_, 1, v___x_3007_);
lean_ctor_set(v___x_3433_, 2, v___x_3430_);
lean_ctor_set(v___x_3433_, 3, v___x_3431_);
lean_ctor_set(v___x_3433_, 4, v___x_3432_);
lean_ctor_set(v___x_3433_, 5, v___x_3428_);
lean_ctor_set(v___x_3433_, 6, v___x_3432_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*7, v___x_3342_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*7 + 1, v___x_3342_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*7 + 2, v___x_3342_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*7 + 3, v_hasTrace_3015_);
v___x_3434_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3436_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3434_);
lean_ctor_set(v___x_3437_, 1, v___x_3435_);
lean_ctor_set(v___x_3437_, 2, v___x_3007_);
lean_ctor_set(v___x_3437_, 3, v___x_3429_);
lean_ctor_set(v___x_3437_, 4, v___x_3436_);
v___x_3438_ = lean_st_mk_ref(v___x_3437_);
v___x_3439_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3350_, v___x_3433_, v___x_3438_, v___y_3010_, v___y_3011_);
lean_dec_ref_known(v___x_3433_, 7);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = lean_st_ref_get(v___x_3438_);
lean_dec(v___x_3438_);
lean_dec(v___x_3441_);
v_a_3362_ = v_a_3440_;
goto v___jp_3361_;
}
else
{
lean_dec(v___x_3438_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3442_; 
v_a_3442_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3439_, 1);
v_a_3362_ = v_a_3442_;
goto v___jp_3361_;
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_del_object(v___x_3348_);
v_a_3443_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3439_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3439_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
v___jp_3361_:
{
if (lean_obj_tag(v_a_3362_) == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = lean_box(v___x_3342_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set_tag(v___x_3348_, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3363_);
v___x_3365_ = v___x_3348_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
else
{
lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3374_; 
lean_del_object(v___x_3348_);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_a_3362_);
if (v_isSharedCheck_3374_ == 0)
{
lean_object* v_unused_3375_; 
v_unused_3375_ = lean_ctor_get(v_a_3362_, 0);
lean_dec(v_unused_3375_);
v___x_3368_ = v_a_3362_;
v_isShared_3369_ = v_isSharedCheck_3374_;
goto v_resetjp_3367_;
}
else
{
lean_dec(v_a_3362_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3374_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_box(v___x_3360_);
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
}
}
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec(v___x_3345_);
lean_dec(v_name_3009_);
lean_dec(v___x_3007_);
v___x_3452_ = lean_box(v___x_3342_);
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
else
{
goto v___jp_3213_;
}
}
else
{
goto v___jp_3213_;
}
v___jp_3133_:
{
lean_object* v___x_3137_; double v___x_3138_; double v___x_3139_; double v___x_3140_; double v___x_3141_; double v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3137_ = lean_io_mono_nanos_now();
v___x_3138_ = lean_float_of_nat(v___y_3135_);
v___x_3139_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3140_ = lean_float_div(v___x_3138_, v___x_3139_);
v___x_3141_ = lean_float_of_nat(v___x_3137_);
v___x_3142_ = lean_float_div(v___x_3141_, v___x_3139_);
v___x_3143_ = lean_box_float(v___x_3140_);
v___x_3144_ = lean_box_float(v___x_3142_);
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3143_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v_a_3136_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3129_, v_hasTrace_3015_, v___x_3130_, v_options_3014_, v___x_3132_, v___y_3134_, v___f_3128_, v___x_3146_, v___y_3010_, v___y_3011_);
return v___x_3147_;
}
v___jp_3148_:
{
lean_object* v___x_3152_; 
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v_a_3151_);
v___y_3134_ = v___y_3149_;
v___y_3135_ = v___y_3150_;
v_a_3136_ = v___x_3152_;
goto v___jp_3133_;
}
v___jp_3153_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_box(v_a_3156_);
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
v___y_3134_ = v___y_3154_;
v___y_3135_ = v___y_3155_;
v_a_3136_ = v___x_3158_;
goto v___jp_3133_;
}
v___jp_3159_:
{
if (lean_obj_tag(v_a_3164_) == 0)
{
v___y_3154_ = v___y_3162_;
v___y_3155_ = v___y_3163_;
v_a_3156_ = v___y_3160_;
goto v___jp_3153_;
}
else
{
lean_dec_ref_known(v_a_3164_, 1);
v___y_3154_ = v___y_3162_;
v___y_3155_ = v___y_3163_;
v_a_3156_ = v___y_3161_;
goto v___jp_3153_;
}
}
v___jp_3165_:
{
if (lean_obj_tag(v_a_3170_) == 0)
{
v___y_3154_ = v___y_3168_;
v___y_3155_ = v___y_3169_;
v_a_3156_ = v___y_3167_;
goto v___jp_3153_;
}
else
{
lean_dec_ref_known(v_a_3170_, 1);
v___y_3154_ = v___y_3168_;
v___y_3155_ = v___y_3169_;
v_a_3156_ = v___y_3166_;
goto v___jp_3153_;
}
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
v___x_3182_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3129_, v_hasTrace_3015_, v___x_3130_, v_options_3014_, v___x_3132_, v___y_3173_, v___f_3128_, v___x_3181_, v___y_3010_, v___y_3011_);
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
v___y_3184_ = v___y_3191_;
v___y_3185_ = v___y_3193_;
v_a_3186_ = v___y_3190_;
goto v___jp_3183_;
}
else
{
lean_dec_ref_known(v_a_3194_, 1);
v___y_3184_ = v___y_3191_;
v___y_3185_ = v___y_3193_;
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
v___y_3184_ = v___y_3197_;
v___y_3185_ = v___y_3198_;
v_a_3186_ = v___x_3200_;
goto v___jp_3183_;
}
else
{
lean_dec_ref_known(v_a_3199_, 1);
v___y_3184_ = v___y_3197_;
v___y_3185_ = v___y_3198_;
v_a_3186_ = v___y_3196_;
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
v___x_3214_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3011_);
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref(v___x_3214_);
v___x_3216_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3217_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3014_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v_env_3220_; lean_object* v___x_3221_; 
lean_dec_ref(v___f_3008_);
v___x_3218_ = lean_io_mono_nanos_now();
v___x_3219_ = lean_st_ref_get(v___y_3011_);
v_env_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc_ref(v_env_3220_);
lean_dec(v___x_3219_);
lean_inc(v_name_3009_);
v___x_3221_ = l_Lean_Meta_declFromEqLikeName(v_env_3220_, v_name_3009_);
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
v___x_3225_ = lean_st_ref_get(v___y_3011_);
v_env_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc_ref(v_env_3226_);
lean_dec(v___x_3225_);
v___x_3227_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3226_, v_fst_3223_, v_snd_3224_);
v___x_3228_ = lean_name_eq(v_name_3009_, v___x_3227_);
lean_dec(v___x_3227_);
lean_dec(v_name_3009_);
if (v___x_3228_ == 0)
{
lean_dec(v_snd_3224_);
lean_dec(v_fst_3223_);
lean_dec(v___x_3007_);
v___y_3154_ = v_a_3215_;
v___y_3155_ = v___x_3218_;
v_a_3156_ = v___x_3217_;
goto v___jp_3153_;
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
lean_dec(v___x_3007_);
v___y_3154_ = v_a_3215_;
v___y_3155_ = v___x_3218_;
v_a_3156_ = v___x_3217_;
goto v___jp_3153_;
}
else
{
uint8_t v___x_3232_; uint8_t v___x_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; uint64_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3232_ = 1;
v___x_3233_ = 0;
v___x_3234_ = 2;
v___x_3235_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3235_, 0, v___x_3229_);
lean_ctor_set_uint8(v___x_3235_, 1, v___x_3229_);
lean_ctor_set_uint8(v___x_3235_, 2, v___x_3229_);
lean_ctor_set_uint8(v___x_3235_, 3, v___x_3229_);
lean_ctor_set_uint8(v___x_3235_, 4, v___x_3229_);
lean_ctor_set_uint8(v___x_3235_, 5, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 6, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 7, v___x_3229_);
lean_ctor_set_uint8(v___x_3235_, 8, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 9, v___x_3232_);
lean_ctor_set_uint8(v___x_3235_, 10, v___x_3233_);
lean_ctor_set_uint8(v___x_3235_, 11, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 12, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 13, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 14, v___x_3234_);
lean_ctor_set_uint8(v___x_3235_, 15, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 16, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 17, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 18, v___x_3231_);
lean_ctor_set_uint8(v___x_3235_, 19, v___x_3229_);
v___x_3236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3235_);
v___x_3237_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set_uint64(v___x_3237_, sizeof(void*)*1, v___x_3236_);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3240_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3241_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3242_ = lean_box(0);
lean_inc(v___x_3007_);
v___x_3243_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3243_, 0, v___x_3237_);
lean_ctor_set(v___x_3243_, 1, v___x_3007_);
lean_ctor_set(v___x_3243_, 2, v___x_3240_);
lean_ctor_set(v___x_3243_, 3, v___x_3241_);
lean_ctor_set(v___x_3243_, 4, v___x_3242_);
lean_ctor_set(v___x_3243_, 5, v___x_3238_);
lean_ctor_set(v___x_3243_, 6, v___x_3242_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7, v___x_3229_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 1, v___x_3229_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 2, v___x_3229_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*7 + 3, v_hasTrace_3015_);
v___x_3244_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3245_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3246_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3244_);
lean_ctor_set(v___x_3247_, 1, v___x_3245_);
lean_ctor_set(v___x_3247_, 2, v___x_3007_);
lean_ctor_set(v___x_3247_, 3, v___x_3239_);
lean_ctor_set(v___x_3247_, 4, v___x_3246_);
v___x_3248_ = lean_st_mk_ref(v___x_3247_);
v___x_3249_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3223_, v_hasTrace_3015_, v___x_3243_, v___x_3248_, v___y_3010_, v___y_3011_);
lean_dec_ref_known(v___x_3243_, 7);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3251_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3249_, 1);
v___x_3251_ = lean_st_ref_get(v___x_3248_);
lean_dec(v___x_3248_);
lean_dec(v___x_3251_);
v___y_3166_ = v___x_3231_;
v___y_3167_ = v___x_3229_;
v___y_3168_ = v_a_3215_;
v___y_3169_ = v___x_3218_;
v_a_3170_ = v_a_3250_;
goto v___jp_3165_;
}
else
{
lean_dec(v___x_3248_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3252_; 
v_a_3252_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3249_, 1);
v___y_3166_ = v___x_3231_;
v___y_3167_ = v___x_3229_;
v___y_3168_ = v_a_3215_;
v___y_3169_ = v___x_3218_;
v_a_3170_ = v_a_3252_;
goto v___jp_3165_;
}
else
{
lean_object* v_a_3253_; 
v_a_3253_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3249_, 1);
v___y_3149_ = v_a_3215_;
v___y_3150_ = v___x_3218_;
v_a_3151_ = v_a_3253_;
goto v___jp_3148_;
}
}
}
}
else
{
uint8_t v___x_3254_; uint8_t v___x_3255_; uint8_t v___x_3256_; lean_object* v___x_3257_; uint64_t v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec(v_snd_3224_);
v___x_3254_ = 1;
v___x_3255_ = 0;
v___x_3256_ = 2;
v___x_3257_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3257_, 0, v___x_3217_);
lean_ctor_set_uint8(v___x_3257_, 1, v___x_3217_);
lean_ctor_set_uint8(v___x_3257_, 2, v___x_3217_);
lean_ctor_set_uint8(v___x_3257_, 3, v___x_3217_);
lean_ctor_set_uint8(v___x_3257_, 4, v___x_3217_);
lean_ctor_set_uint8(v___x_3257_, 5, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 6, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 7, v___x_3217_);
lean_ctor_set_uint8(v___x_3257_, 8, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 9, v___x_3254_);
lean_ctor_set_uint8(v___x_3257_, 10, v___x_3255_);
lean_ctor_set_uint8(v___x_3257_, 11, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 12, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 13, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 14, v___x_3256_);
lean_ctor_set_uint8(v___x_3257_, 15, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 16, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 17, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 18, v___x_3229_);
lean_ctor_set_uint8(v___x_3257_, 19, v___x_3217_);
v___x_3258_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3257_);
v___x_3259_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set_uint64(v___x_3259_, sizeof(void*)*1, v___x_3258_);
v___x_3260_ = lean_unsigned_to_nat(0u);
v___x_3261_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3262_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3263_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3264_ = lean_box(0);
lean_inc(v___x_3007_);
v___x_3265_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3265_, 0, v___x_3259_);
lean_ctor_set(v___x_3265_, 1, v___x_3007_);
lean_ctor_set(v___x_3265_, 2, v___x_3262_);
lean_ctor_set(v___x_3265_, 3, v___x_3263_);
lean_ctor_set(v___x_3265_, 4, v___x_3264_);
lean_ctor_set(v___x_3265_, 5, v___x_3260_);
lean_ctor_set(v___x_3265_, 6, v___x_3264_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*7, v___x_3217_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*7 + 1, v___x_3217_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*7 + 2, v___x_3217_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*7 + 3, v_hasTrace_3015_);
v___x_3266_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3267_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3268_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3266_);
lean_ctor_set(v___x_3269_, 1, v___x_3267_);
lean_ctor_set(v___x_3269_, 2, v___x_3007_);
lean_ctor_set(v___x_3269_, 3, v___x_3261_);
lean_ctor_set(v___x_3269_, 4, v___x_3268_);
v___x_3270_ = lean_st_mk_ref(v___x_3269_);
v___x_3271_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3223_, v___x_3265_, v___x_3270_, v___y_3010_, v___y_3011_);
lean_dec_ref_known(v___x_3265_, 7);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = lean_st_ref_get(v___x_3270_);
lean_dec(v___x_3270_);
lean_dec(v___x_3273_);
v___y_3160_ = v___x_3217_;
v___y_3161_ = v___x_3229_;
v___y_3162_ = v_a_3215_;
v___y_3163_ = v___x_3218_;
v_a_3164_ = v_a_3272_;
goto v___jp_3159_;
}
else
{
lean_dec(v___x_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3274_; 
v_a_3274_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3271_, 1);
v___y_3160_ = v___x_3217_;
v___y_3161_ = v___x_3229_;
v___y_3162_ = v_a_3215_;
v___y_3163_ = v___x_3218_;
v_a_3164_ = v_a_3274_;
goto v___jp_3159_;
}
else
{
lean_object* v_a_3275_; 
v_a_3275_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3271_, 1);
v___y_3149_ = v_a_3215_;
v___y_3150_ = v___x_3218_;
v_a_3151_ = v_a_3275_;
goto v___jp_3148_;
}
}
}
}
}
else
{
lean_dec(v___x_3221_);
lean_dec(v_name_3009_);
lean_dec(v___x_3007_);
v___y_3154_ = v_a_3215_;
v___y_3155_ = v___x_3218_;
v_a_3156_ = v___x_3217_;
goto v___jp_3153_;
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v_env_3278_; lean_object* v___x_3279_; 
v___x_3276_ = lean_io_get_num_heartbeats();
v___x_3277_ = lean_st_ref_get(v___y_3011_);
v_env_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc_ref(v_env_3278_);
lean_dec(v___x_3277_);
lean_inc(v_name_3009_);
v___x_3279_ = l_Lean_Meta_declFromEqLikeName(v_env_3278_, v_name_3009_);
if (lean_obj_tag(v___x_3279_) == 1)
{
lean_object* v_val_3280_; lean_object* v_fst_3281_; lean_object* v_snd_3282_; lean_object* v___x_3283_; lean_object* v_env_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
v_val_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_val_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v_fst_3281_ = lean_ctor_get(v_val_3280_, 0);
lean_inc_n(v_fst_3281_, 2);
v_snd_3282_ = lean_ctor_get(v_val_3280_, 1);
lean_inc_n(v_snd_3282_, 2);
lean_dec(v_val_3280_);
v___x_3283_ = lean_st_ref_get(v___y_3011_);
v_env_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc_ref(v_env_3284_);
lean_dec(v___x_3283_);
v___x_3285_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3284_, v_fst_3281_, v_snd_3282_);
v___x_3286_ = lean_name_eq(v_name_3009_, v___x_3285_);
lean_dec(v___x_3285_);
lean_dec(v_name_3009_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_dec(v_snd_3282_);
lean_dec(v_fst_3281_);
lean_dec(v___x_3007_);
v___x_3287_ = lean_box(0);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
v___x_3288_ = lean_apply_4(v___f_3008_, v___x_3287_, v___y_3010_, v___y_3011_, lean_box(0));
v___y_3207_ = v___x_3276_;
v___y_3208_ = v_a_3215_;
v___y_3209_ = v___x_3288_;
goto v___jp_3206_;
}
else
{
uint8_t v___x_3289_; 
lean_inc(v_snd_3282_);
v___x_3289_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3282_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3290_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3291_ = lean_string_dec_eq(v_snd_3282_, v___x_3290_);
lean_dec(v_snd_3282_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec(v_fst_3281_);
lean_dec(v___x_3007_);
v___x_3292_ = lean_box(0);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
v___x_3293_ = lean_apply_4(v___f_3008_, v___x_3292_, v___y_3010_, v___y_3011_, lean_box(0));
v___y_3207_ = v___x_3276_;
v___y_3208_ = v_a_3215_;
v___y_3209_ = v___x_3293_;
goto v___jp_3206_;
}
else
{
uint8_t v___x_3294_; uint8_t v___x_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; uint64_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec_ref(v___f_3008_);
v___x_3294_ = 1;
v___x_3295_ = 0;
v___x_3296_ = 2;
v___x_3297_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3297_, 0, v___x_3289_);
lean_ctor_set_uint8(v___x_3297_, 1, v___x_3289_);
lean_ctor_set_uint8(v___x_3297_, 2, v___x_3289_);
lean_ctor_set_uint8(v___x_3297_, 3, v___x_3289_);
lean_ctor_set_uint8(v___x_3297_, 4, v___x_3289_);
lean_ctor_set_uint8(v___x_3297_, 5, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 6, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 7, v___x_3289_);
lean_ctor_set_uint8(v___x_3297_, 8, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 9, v___x_3294_);
lean_ctor_set_uint8(v___x_3297_, 10, v___x_3295_);
lean_ctor_set_uint8(v___x_3297_, 11, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 12, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 13, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 14, v___x_3296_);
lean_ctor_set_uint8(v___x_3297_, 15, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 16, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 17, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 18, v___x_3291_);
lean_ctor_set_uint8(v___x_3297_, 19, v___x_3289_);
v___x_3298_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3297_);
v___x_3299_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set_uint64(v___x_3299_, sizeof(void*)*1, v___x_3298_);
v___x_3300_ = lean_unsigned_to_nat(0u);
v___x_3301_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3302_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3304_ = lean_box(0);
lean_inc(v___x_3007_);
v___x_3305_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3305_, 0, v___x_3299_);
lean_ctor_set(v___x_3305_, 1, v___x_3007_);
lean_ctor_set(v___x_3305_, 2, v___x_3302_);
lean_ctor_set(v___x_3305_, 3, v___x_3303_);
lean_ctor_set(v___x_3305_, 4, v___x_3304_);
lean_ctor_set(v___x_3305_, 5, v___x_3300_);
lean_ctor_set(v___x_3305_, 6, v___x_3304_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*7, v___x_3289_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*7 + 1, v___x_3289_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*7 + 2, v___x_3289_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*7 + 3, v___x_3217_);
v___x_3306_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3307_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3308_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3306_);
lean_ctor_set(v___x_3309_, 1, v___x_3307_);
lean_ctor_set(v___x_3309_, 2, v___x_3007_);
lean_ctor_set(v___x_3309_, 3, v___x_3301_);
lean_ctor_set(v___x_3309_, 4, v___x_3308_);
v___x_3310_ = lean_st_mk_ref(v___x_3309_);
v___x_3311_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3281_, v___x_3217_, v___x_3305_, v___x_3310_, v___y_3010_, v___y_3011_);
lean_dec_ref_known(v___x_3305_, 7);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = lean_st_ref_get(v___x_3310_);
lean_dec(v___x_3310_);
lean_dec(v___x_3313_);
v___y_3190_ = v___x_3289_;
v___y_3191_ = v___x_3276_;
v___y_3192_ = v___x_3291_;
v___y_3193_ = v_a_3215_;
v_a_3194_ = v_a_3312_;
goto v___jp_3189_;
}
else
{
lean_dec(v___x_3310_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3314_; 
v_a_3314_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3311_, 1);
v___y_3190_ = v___x_3289_;
v___y_3191_ = v___x_3276_;
v___y_3192_ = v___x_3291_;
v___y_3193_ = v_a_3215_;
v_a_3194_ = v_a_3314_;
goto v___jp_3189_;
}
else
{
lean_object* v_a_3315_; 
v_a_3315_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3315_);
lean_dec_ref_known(v___x_3311_, 1);
v___y_3202_ = v___x_3276_;
v___y_3203_ = v_a_3215_;
v_a_3204_ = v_a_3315_;
goto v___jp_3201_;
}
}
}
}
else
{
uint8_t v___x_3316_; uint8_t v___x_3317_; uint8_t v___x_3318_; uint8_t v___x_3319_; lean_object* v___x_3320_; uint64_t v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec(v_snd_3282_);
lean_dec_ref(v___f_3008_);
v___x_3316_ = 0;
v___x_3317_ = 1;
v___x_3318_ = 0;
v___x_3319_ = 2;
v___x_3320_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3320_, 0, v___x_3316_);
lean_ctor_set_uint8(v___x_3320_, 1, v___x_3316_);
lean_ctor_set_uint8(v___x_3320_, 2, v___x_3316_);
lean_ctor_set_uint8(v___x_3320_, 3, v___x_3316_);
lean_ctor_set_uint8(v___x_3320_, 4, v___x_3316_);
lean_ctor_set_uint8(v___x_3320_, 5, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 6, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 7, v___x_3316_);
lean_ctor_set_uint8(v___x_3320_, 8, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 9, v___x_3317_);
lean_ctor_set_uint8(v___x_3320_, 10, v___x_3318_);
lean_ctor_set_uint8(v___x_3320_, 11, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 12, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 13, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 14, v___x_3319_);
lean_ctor_set_uint8(v___x_3320_, 15, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 16, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 17, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 18, v___x_3289_);
lean_ctor_set_uint8(v___x_3320_, 19, v___x_3316_);
v___x_3321_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3320_);
v___x_3322_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set_uint64(v___x_3322_, sizeof(void*)*1, v___x_3321_);
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3324_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3325_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3326_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3327_ = lean_box(0);
lean_inc(v___x_3007_);
v___x_3328_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3328_, 0, v___x_3322_);
lean_ctor_set(v___x_3328_, 1, v___x_3007_);
lean_ctor_set(v___x_3328_, 2, v___x_3325_);
lean_ctor_set(v___x_3328_, 3, v___x_3326_);
lean_ctor_set(v___x_3328_, 4, v___x_3327_);
lean_ctor_set(v___x_3328_, 5, v___x_3323_);
lean_ctor_set(v___x_3328_, 6, v___x_3327_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*7, v___x_3316_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*7 + 1, v___x_3316_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*7 + 2, v___x_3316_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*7 + 3, v___x_3217_);
v___x_3329_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3330_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3331_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3329_);
lean_ctor_set(v___x_3332_, 1, v___x_3330_);
lean_ctor_set(v___x_3332_, 2, v___x_3007_);
lean_ctor_set(v___x_3332_, 3, v___x_3324_);
lean_ctor_set(v___x_3332_, 4, v___x_3331_);
v___x_3333_ = lean_st_mk_ref(v___x_3332_);
v___x_3334_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3281_, v___x_3328_, v___x_3333_, v___y_3010_, v___y_3011_);
lean_dec_ref_known(v___x_3328_, 7);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
v___x_3336_ = lean_st_ref_get(v___x_3333_);
lean_dec(v___x_3333_);
lean_dec(v___x_3336_);
v___y_3196_ = v___x_3289_;
v___y_3197_ = v___x_3276_;
v___y_3198_ = v_a_3215_;
v_a_3199_ = v_a_3335_;
goto v___jp_3195_;
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
v___y_3196_ = v___x_3289_;
v___y_3197_ = v___x_3276_;
v___y_3198_ = v_a_3215_;
v_a_3199_ = v_a_3337_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3338_; 
v_a_3338_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3334_, 1);
v___y_3202_ = v___x_3276_;
v___y_3203_ = v_a_3215_;
v_a_3204_ = v_a_3338_;
goto v___jp_3201_;
}
}
}
}
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_dec(v___x_3279_);
lean_dec(v_name_3009_);
lean_dec(v___x_3007_);
v___x_3339_ = lean_box(0);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
v___x_3340_ = lean_apply_4(v___f_3008_, v___x_3339_, v___y_3010_, v___y_3011_, lean_box(0));
v___y_3207_ = v___x_3276_;
v___y_3208_ = v_a_3215_;
v___y_3209_ = v___x_3340_;
goto v___jp_3206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3454_, lean_object* v___f_3455_, lean_object* v_name_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3454_, v___f_3455_, v_name_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
return v_res_3460_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = lean_unsigned_to_nat(3137104340u);
v___x_3506_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3507_ = l_Lean_Name_num___override(v___x_3506_, v___x_3505_);
return v___x_3507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3510_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3511_ = l_Lean_Name_str___override(v___x_3510_, v___x_3509_);
return v___x_3511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3514_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3515_ = l_Lean_Name_str___override(v___x_3514_, v___x_3513_);
return v___x_3515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = lean_unsigned_to_nat(2u);
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3518_ = l_Lean_Name_num___override(v___x_3517_, v___x_3516_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3520_; lean_object* v___x_3521_; 
v___f_3520_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3521_ = l_Lean_registerReservedNameAction(v___f_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3522_; uint8_t v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec_ref_known(v___x_3521_, 1);
v___x_3522_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3523_ = 0;
v___x_3524_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3525_ = l_Lean_registerTraceClass(v___x_3522_, v___x_3523_, v___x_3524_);
return v___x_3525_;
}
else
{
return v___x_3521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3528_, lean_object* v_x_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3529_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3534_, lean_object* v_x_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3534_, v_x_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
return v_res_3539_;
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
