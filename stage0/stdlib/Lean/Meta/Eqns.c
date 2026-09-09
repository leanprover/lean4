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
lean_object* v___x_313_; lean_object* v_env_314_; lean_object* v_options_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_313_ = lean_st_ref_get(v___y_311_);
v_env_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_env_314_);
lean_dec(v___x_313_);
v_options_315_ = lean_ctor_get(v___y_310_, 1);
v___x_316_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_315_);
v___x_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_318_, 0, v_env_314_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
lean_ctor_set(v___x_318_, 3, v_options_315_);
v___x_319_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_msgData_309_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_ref_330_ = lean_ctor_get(v___y_327_, 4);
v___x_331_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_326_, v___y_327_, v___y_328_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
lean_inc(v_ref_330_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_ref_330_);
lean_ctor_set(v___x_336_, 1, v_a_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set_tag(v___x_334_, 1);
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_345_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0));
v___x_348_ = l_Lean_stringToMessageData(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* v_declName_355_, lean_object* v_reservedName_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_360_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
v___x_361_ = 0;
v___x_362_ = l_Lean_MessageData_ofConstName(v_declName_355_, v___x_361_);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_360_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
v___x_365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = 1;
v___x_367_ = l_Lean_MessageData_ofConstName(v_reservedName_356_, v___x_366_);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_365_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5, &l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
v___x_370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_370_, v___y_357_, v___y_358_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* v_declName_372_, lean_object* v_reservedName_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_372_, v_reservedName_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* v_declName_378_, lean_object* v_suffix_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; lean_object* v_env_384_; lean_object* v_reservedName_385_; uint8_t v___x_386_; uint8_t v___x_387_; 
v___x_383_ = lean_st_ref_get(v___y_381_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_383_);
lean_inc(v_declName_378_);
v_reservedName_385_ = l_Lean_Name_str___override(v_declName_378_, v_suffix_379_);
v___x_386_ = 1;
lean_inc(v_reservedName_385_);
v___x_387_ = l_Lean_Environment_contains(v_env_384_, v_reservedName_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_reservedName_385_);
lean_dec(v_declName_378_);
v___x_388_ = lean_box(0);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_378_, v_reservedName_385_, v___y_380_, v___y_381_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* v_declName_391_, lean_object* v_suffix_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_391_, v_suffix_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* v_declName_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Meta_eqUnfoldThmSuffix___closed__0));
lean_inc(v_declName_397_);
v___x_402_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_397_, v___x_401_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref_known(v___x_402_, 1);
v___x_403_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_397_);
v___x_404_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_397_, v___x_403_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref_known(v___x_404_, 1);
v___x_405_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
v___x_406_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_397_, v___x_405_, v_a_398_, v_a_399_);
return v___x_406_;
}
else
{
lean_dec(v_declName_397_);
return v___x_404_;
}
}
else
{
lean_dec(v_declName_397_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* v_declName_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_412_, lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_413_, v___y_414_, v___y_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_418_, lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_418_, v_msg_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(lean_object* v_env_424_, lean_object* v_n_425_){
_start:
{
lean_object* v___x_426_; 
lean_inc(v_n_425_);
lean_inc_ref(v_env_424_);
v___x_426_ = l_Lean_Meta_declFromEqLikeName(v_env_424_, v_n_425_);
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_val_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_val_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v___x_426_, 1);
v_fst_428_ = lean_ctor_get(v_val_427_, 0);
lean_inc(v_fst_428_);
v_snd_429_ = lean_ctor_get(v_val_427_, 1);
lean_inc(v_snd_429_);
lean_dec(v_val_427_);
v___x_430_ = l_Lean_Meta_mkEqLikeNameFor(v_env_424_, v_fst_428_, v_snd_429_);
v___x_431_ = lean_name_eq(v_n_425_, v___x_430_);
lean_dec(v___x_430_);
lean_dec(v_n_425_);
return v___x_431_;
}
else
{
uint8_t v___x_432_; 
lean_dec(v___x_426_);
lean_dec(v_n_425_);
lean_dec_ref(v_env_424_);
v___x_432_ = 0;
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_env_433_, lean_object* v_n_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_433_, v_n_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_439_; lean_object* v___x_440_; 
v___f_439_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_));
v___x_440_ = l_Lean_registerReservedNamePredicate(v___f_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_box(0);
v___x_445_ = lean_st_mk_ref(v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
return v_res_448_;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_registerGetEqnsFn___closed__0));
v___x_451_ = lean_mk_io_user_error(v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* v_f_452_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = l_Lean_initializing();
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec_ref(v_f_452_);
v___x_455_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_457_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_458_ = lean_st_ref_take(v___x_457_);
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v_f_452_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_st_ref_put(v___x_457_, v___x_459_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___boxed(lean_object* v_f_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Meta_registerGetEqnsFn(v_f_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* v_declName_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_475_; lean_object* v_env_476_; uint8_t v___x_477_; lean_object* v___x_478_; 
v___x_475_ = lean_st_ref_get(v_a_469_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_475_);
v___x_477_ = 0;
lean_inc(v_declName_465_);
v___x_478_ = l_Lean_Environment_findAsync_x3f(v_env_476_, v_declName_465_, v___x_477_);
if (lean_obj_tag(v___x_478_) == 1)
{
lean_object* v_val_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_510_; 
v_val_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_510_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_510_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_val_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_510_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint8_t v_kind_483_; 
v_kind_483_ = lean_ctor_get_uint8(v_val_479_, sizeof(void*)*3);
if (v_kind_483_ == 0)
{
lean_object* v_sig_484_; lean_object* v___x_485_; lean_object* v_env_486_; uint8_t v___x_487_; 
v_sig_484_ = lean_ctor_get(v_val_479_, 1);
lean_inc_ref(v_sig_484_);
lean_dec(v_val_479_);
v___x_485_ = lean_st_ref_get(v_a_469_);
v_env_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref(v_env_486_);
lean_dec(v___x_485_);
v___x_487_ = l_Lean_Meta_isMatcherCore(v_env_486_, v_declName_465_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v_type_489_; lean_object* v___x_490_; 
lean_del_object(v___x_481_);
v___x_488_ = lean_task_get_own(v_sig_484_);
v_type_489_ = lean_ctor_get(v___x_488_, 2);
lean_inc_ref(v_type_489_);
lean_dec(v___x_488_);
v___x_490_ = l_Lean_Meta_isProp(v_type_489_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_505_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_505_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_505_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_505_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v___x_495_; 
v___x_495_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
if (v___x_495_ == 0)
{
uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_496_ = 1;
v___x_497_ = lean_box(v___x_496_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_499_ = v___x_493_;
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
else
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_box(v___x_487_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_501_);
v___x_503_ = v___x_493_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
return v___x_490_;
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec_ref(v_sig_484_);
v___x_506_ = lean_box(v___x_477_);
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 0);
lean_ctor_set(v___x_481_, 0, v___x_506_);
v___x_508_ = v___x_481_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
else
{
lean_del_object(v___x_481_);
lean_dec(v_val_479_);
lean_dec(v_declName_465_);
goto v___jp_471_;
}
}
}
else
{
lean_dec(v___x_478_);
lean_dec(v_declName_465_);
goto v___jp_471_;
}
v___jp_471_:
{
uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = 0;
v___x_473_ = lean_box(v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(lean_object* v_declName_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
return v_res_517_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0(void){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_518_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState_default(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(lean_object* v___x_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v___x_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_526_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_529_; lean_object* v___f_530_; 
v___x_529_ = lean_obj_once(&l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1, &l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once, _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1);
v___f_530_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_530_, 0, v___x_529_);
return v___f_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___f_532_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_box(1);
v___x_535_ = l_Lean_registerEnvExtension___redArg(v___f_532_, v___x_533_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
return v_res_537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(lean_object* v_opts_538_, lean_object* v_opt_539_){
_start:
{
lean_object* v_name_540_; lean_object* v_defValue_541_; lean_object* v_map_542_; lean_object* v___x_543_; 
v_name_540_ = lean_ctor_get(v_opt_539_, 0);
v_defValue_541_ = lean_ctor_get(v_opt_539_, 1);
v_map_542_ = lean_ctor_get(v_opts_538_, 0);
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_542_, v_name_540_);
if (lean_obj_tag(v___x_543_) == 0)
{
uint8_t v___x_544_; 
v___x_544_ = lean_unbox(v_defValue_541_);
return v___x_544_;
}
else
{
lean_object* v_val_545_; 
v_val_545_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_543_, 1);
if (lean_obj_tag(v_val_545_) == 1)
{
uint8_t v_v_546_; 
v_v_546_ = lean_ctor_get_uint8(v_val_545_, 0);
lean_dec_ref_known(v_val_545_, 0);
return v_v_546_;
}
else
{
uint8_t v___x_547_; 
lean_dec(v_val_545_);
v___x_547_ = lean_unbox(v_defValue_541_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(lean_object* v_opts_548_, lean_object* v_opt_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_548_, v_opt_549_);
lean_dec_ref(v_opt_549_);
lean_dec_ref(v_opts_548_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(lean_object* v_opts_552_, lean_object* v_opt_553_){
_start:
{
lean_object* v_name_554_; lean_object* v_defValue_555_; lean_object* v_map_556_; lean_object* v___x_557_; 
v_name_554_ = lean_ctor_get(v_opt_553_, 0);
v_defValue_555_ = lean_ctor_get(v_opt_553_, 1);
v_map_556_ = lean_ctor_get(v_opts_552_, 0);
v___x_557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_556_, v_name_554_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_inc(v_defValue_555_);
return v_defValue_555_;
}
else
{
lean_object* v_val_558_; 
v_val_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v___x_557_, 1);
if (lean_obj_tag(v_val_558_) == 3)
{
lean_object* v_v_559_; 
v_v_559_ = lean_ctor_get(v_val_558_, 0);
lean_inc(v_v_559_);
lean_dec_ref_known(v_val_558_, 1);
return v_v_559_;
}
else
{
lean_dec(v_val_558_);
lean_inc(v_defValue_555_);
return v_defValue_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(lean_object* v_opts_560_, lean_object* v_opt_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_560_, v_opt_561_);
lean_dec_ref(v_opt_561_);
lean_dec_ref(v_opts_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(lean_object* v_as_566_, size_t v_sz_567_, size_t v_i_568_, lean_object* v_b_569_){
_start:
{
lean_object* v_a_571_; uint8_t v___x_575_; 
v___x_575_ = lean_usize_dec_lt(v_i_568_, v_sz_567_);
if (v___x_575_ == 0)
{
return v_b_569_;
}
else
{
lean_object* v_a_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v_map_579_; uint8_t v_hasTrace_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_593_; 
v_a_576_ = lean_array_uget_borrowed(v_as_566_, v_i_568_);
v_fst_577_ = lean_ctor_get(v_a_576_, 0);
v_snd_578_ = lean_ctor_get(v_a_576_, 1);
v_map_579_ = lean_ctor_get(v_b_569_, 0);
v_hasTrace_580_ = lean_ctor_get_uint8(v_b_569_, sizeof(void*)*1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_b_569_);
if (v_isSharedCheck_593_ == 0)
{
v___x_582_ = v_b_569_;
v_isShared_583_ = v_isSharedCheck_593_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_map_579_);
lean_dec(v_b_569_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_593_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; 
lean_inc(v_snd_578_);
lean_inc(v_fst_577_);
v___x_584_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_577_, v_snd_578_, v_map_579_);
if (v_hasTrace_580_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_588_; 
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_586_ = l_Lean_Name_isPrefixOf(v___x_585_, v_fst_577_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_584_);
v___x_588_ = v___x_582_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_584_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*1, v___x_586_);
v_a_571_ = v___x_588_;
goto v___jp_570_;
}
}
else
{
lean_object* v___x_591_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_584_);
v___x_591_ = v___x_582_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_584_);
lean_ctor_set_uint8(v_reuseFailAlloc_592_, sizeof(void*)*1, v_hasTrace_580_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
v_a_571_ = v___x_591_;
goto v___jp_570_;
}
}
}
}
v___jp_570_:
{
size_t v___x_572_; size_t v___x_573_; 
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_i_568_, v___x_572_);
v_i_568_ = v___x_573_;
v_b_569_ = v_a_571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(lean_object* v_as_594_, lean_object* v_sz_595_, lean_object* v_i_596_, lean_object* v_b_597_){
_start:
{
size_t v_sz_boxed_598_; size_t v_i_boxed_599_; lean_object* v_res_600_; 
v_sz_boxed_598_ = lean_unbox_usize(v_sz_595_);
lean_dec(v_sz_595_);
v_i_boxed_599_ = lean_unbox_usize(v_i_596_);
lean_dec(v_i_596_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_as_594_, v_sz_boxed_598_, v_i_boxed_599_, v_b_597_);
lean_dec_ref(v_as_594_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(lean_object* v_o_601_, lean_object* v_k_602_, uint8_t v_v_603_){
_start:
{
lean_object* v_map_604_; uint8_t v_hasTrace_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_619_; 
v_map_604_ = lean_ctor_get(v_o_601_, 0);
v_hasTrace_605_ = lean_ctor_get_uint8(v_o_601_, sizeof(void*)*1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_o_601_);
if (v_isSharedCheck_619_ == 0)
{
v___x_607_ = v_o_601_;
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_map_604_);
lean_dec(v_o_601_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_609_, 0, v_v_603_);
lean_inc(v_k_602_);
v___x_610_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_602_, v___x_609_, v_map_604_);
if (v_hasTrace_605_ == 0)
{
lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v___x_614_; 
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_612_ = l_Lean_Name_isPrefixOf(v___x_611_, v_k_602_);
lean_dec(v_k_602_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_614_ = v___x_607_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_610_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*1, v___x_612_);
return v___x_614_;
}
}
else
{
lean_object* v___x_617_; 
lean_dec(v_k_602_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_617_ = v___x_607_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_610_);
lean_ctor_set_uint8(v_reuseFailAlloc_618_, sizeof(void*)*1, v_hasTrace_605_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(lean_object* v_o_620_, lean_object* v_k_621_, lean_object* v_v_622_){
_start:
{
uint8_t v_v_boxed_623_; lean_object* v_res_624_; 
v_v_boxed_623_ = lean_unbox(v_v_622_);
v_res_624_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_620_, v_k_621_, v_v_boxed_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(lean_object* v_opts_625_, lean_object* v_opt_626_, uint8_t v_val_627_){
_start:
{
lean_object* v_name_628_; lean_object* v___x_629_; 
v_name_628_ = lean_ctor_get(v_opt_626_, 0);
lean_inc(v_name_628_);
lean_dec_ref(v_opt_626_);
v___x_629_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_625_, v_name_628_, v_val_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(lean_object* v_opts_630_, lean_object* v_opt_631_, lean_object* v_val_632_){
_start:
{
uint8_t v_val_boxed_633_; lean_object* v_res_634_; 
v_val_boxed_633_ = lean_unbox(v_val_632_);
v_res_634_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_opts_630_, v_opt_631_, v_val_boxed_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(lean_object* v_as_635_, size_t v_i_636_, size_t v_stop_637_, lean_object* v_b_638_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_eq(v_i_636_, v_stop_637_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v_defValue_641_; uint8_t v___x_642_; lean_object* v___x_643_; size_t v___x_644_; size_t v___x_645_; 
v___x_640_ = lean_array_uget_borrowed(v_as_635_, v_i_636_);
v_defValue_641_ = lean_ctor_get(v___x_640_, 1);
v___x_642_ = lean_unbox(v_defValue_641_);
lean_inc(v___x_640_);
v___x_643_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(v_b_638_, v___x_640_, v___x_642_);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_636_, v___x_644_);
v_i_636_ = v___x_645_;
v_b_638_ = v___x_643_;
goto _start;
}
else
{
return v_b_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(lean_object* v_as_647_, lean_object* v_i_648_, lean_object* v_stop_649_, lean_object* v_b_650_){
_start:
{
size_t v_i_boxed_651_; size_t v_stop_boxed_652_; lean_object* v_res_653_; 
v_i_boxed_651_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_stop_boxed_652_ = lean_unbox_usize(v_stop_649_);
lean_dec(v_stop_649_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v_as_647_, v_i_boxed_651_, v_stop_boxed_652_, v_b_650_);
lean_dec_ref(v_as_647_);
return v_res_653_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__0(void){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__0, &l_Lean_Meta_withEqnOptions___redArg___closed__0_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__0);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__2(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__3(void){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Array_instInhabited(lean_box(0));
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Meta_withEqnOptions___redArg___closed__4(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = l_Lean_Meta_eqnAffectingOptions;
v___x_661_ = lean_array_get_size(v___x_660_);
return v___x_661_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__5(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_nat_dec_lt(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static uint8_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__6(void){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_666_ = lean_nat_dec_le(v___x_665_, v___x_665_);
return v___x_666_;
}
}
static size_t _init_l_Lean_Meta_withEqnOptions___redArg___closed__7(void){
_start:
{
lean_object* v___x_667_; size_t v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__4, &l_Lean_Meta_withEqnOptions___redArg___closed__4_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__4);
v___x_668_ = lean_usize_of_nat(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg(lean_object* v_declName_669_, lean_object* v_act_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
uint8_t v___y_677_; lean_object* v___y_678_; lean_object* v_toCold_679_; lean_object* v_currRecDepth_680_; lean_object* v_ref_681_; lean_object* v_currNamespace_682_; lean_object* v_openDecls_683_; lean_object* v_initHeartbeats_684_; lean_object* v_maxHeartbeats_685_; lean_object* v_currMacroScope_686_; uint8_t v_suppressElabErrors_687_; lean_object* v___y_688_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_env_695_; lean_object* v___x_696_; lean_object* v_toEnvExtension_697_; lean_object* v_asyncMode_698_; lean_object* v_toCold_699_; lean_object* v_options_700_; lean_object* v_currRecDepth_701_; lean_object* v_ref_702_; lean_object* v_currNamespace_703_; lean_object* v_openDecls_704_; lean_object* v_initHeartbeats_705_; lean_object* v_maxHeartbeats_706_; lean_object* v_currMacroScope_707_; uint8_t v_suppressElabErrors_708_; uint8_t v___y_710_; lean_object* v___y_711_; uint8_t v___y_712_; lean_object* v___y_734_; lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; 
v___x_693_ = lean_st_ref_get(v_a_674_);
v___x_694_ = lean_st_ref_get(v_a_674_);
v_env_695_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_env_695_);
lean_dec(v___x_693_);
v___x_696_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_697_ = lean_ctor_get(v___x_696_, 0);
v_asyncMode_698_ = lean_ctor_get(v_toEnvExtension_697_, 2);
v_toCold_699_ = lean_ctor_get(v_a_673_, 0);
v_options_700_ = lean_ctor_get(v_a_673_, 1);
v_currRecDepth_701_ = lean_ctor_get(v_a_673_, 2);
v_ref_702_ = lean_ctor_get(v_a_673_, 4);
v_currNamespace_703_ = lean_ctor_get(v_a_673_, 5);
v_openDecls_704_ = lean_ctor_get(v_a_673_, 6);
v_initHeartbeats_705_ = lean_ctor_get(v_a_673_, 7);
v_maxHeartbeats_706_ = lean_ctor_get(v_a_673_, 8);
v_currMacroScope_707_ = lean_ctor_get(v_a_673_, 9);
v_suppressElabErrors_708_ = lean_ctor_get_uint8(v_a_673_, sizeof(void*)*10 + 1);
v___x_739_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_740_ = 0;
v___x_741_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_739_, v___x_696_, v_env_695_, v_declName_669_, v_asyncMode_698_, v___x_740_);
if (lean_obj_tag(v___x_741_) == 1)
{
lean_object* v_val_742_; lean_object* v___y_744_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_val_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_748_ = l_Lean_Meta_eqnAffectingOptions;
v___x_749_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_749_ == 0)
{
lean_inc_ref(v_options_700_);
v___y_744_ = v_options_700_;
goto v___jp_743_;
}
else
{
uint8_t v___x_750_; 
v___x_750_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_750_ == 0)
{
if (v___x_749_ == 0)
{
lean_inc_ref(v_options_700_);
v___y_744_ = v_options_700_;
goto v___jp_743_;
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_700_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_748_, v___x_751_, v___x_752_, v_options_700_);
v___y_744_ = v___x_753_;
goto v___jp_743_;
}
}
else
{
size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v___x_754_ = ((size_t)0ULL);
v___x_755_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_700_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_748_, v___x_754_, v___x_755_, v_options_700_);
v___y_744_ = v___x_756_;
goto v___jp_743_;
}
}
v___jp_743_:
{
size_t v_sz_745_; size_t v___x_746_; lean_object* v___x_747_; 
v_sz_745_ = lean_array_size(v_val_742_);
v___x_746_ = ((size_t)0ULL);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_742_, v_sz_745_, v___x_746_, v___y_744_);
lean_dec(v_val_742_);
v___y_734_ = v___x_747_;
goto v___jp_733_;
}
}
else
{
lean_object* v___x_757_; uint8_t v___x_758_; 
lean_dec(v___x_741_);
v___x_757_ = l_Lean_Meta_eqnAffectingOptions;
v___x_758_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_758_ == 0)
{
lean_inc_ref(v_options_700_);
v___y_734_ = v_options_700_;
goto v___jp_733_;
}
else
{
uint8_t v___x_759_; 
v___x_759_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_759_ == 0)
{
if (v___x_758_ == 0)
{
lean_inc_ref(v_options_700_);
v___y_734_ = v_options_700_;
goto v___jp_733_;
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_700_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_757_, v___x_760_, v___x_761_, v_options_700_);
v___y_734_ = v___x_762_;
goto v___jp_733_;
}
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_700_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_757_, v___x_763_, v___x_764_, v_options_700_);
v___y_734_ = v___x_765_;
goto v___jp_733_;
}
}
}
v___jp_676_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_689_ = l_Lean_maxRecDepth;
v___x_690_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_678_, v___x_689_);
lean_inc(v_currMacroScope_686_);
lean_inc(v_maxHeartbeats_685_);
lean_inc(v_initHeartbeats_684_);
lean_inc(v_openDecls_683_);
lean_inc(v_currNamespace_682_);
lean_inc(v_ref_681_);
lean_inc(v_currRecDepth_680_);
lean_inc_ref(v_toCold_679_);
v___x_691_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_691_, 0, v_toCold_679_);
lean_ctor_set(v___x_691_, 1, v___y_678_);
lean_ctor_set(v___x_691_, 2, v_currRecDepth_680_);
lean_ctor_set(v___x_691_, 3, v___x_690_);
lean_ctor_set(v___x_691_, 4, v_ref_681_);
lean_ctor_set(v___x_691_, 5, v_currNamespace_682_);
lean_ctor_set(v___x_691_, 6, v_openDecls_683_);
lean_ctor_set(v___x_691_, 7, v_initHeartbeats_684_);
lean_ctor_set(v___x_691_, 8, v_maxHeartbeats_685_);
lean_ctor_set(v___x_691_, 9, v_currMacroScope_686_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*10, v___y_677_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*10 + 1, v_suppressElabErrors_687_);
lean_inc(v___y_688_);
lean_inc(v_a_672_);
lean_inc_ref(v_a_671_);
v___x_692_ = lean_apply_5(v_act_670_, v_a_671_, v_a_672_, v___x_691_, v___y_688_, lean_box(0));
return v___x_692_;
}
v___jp_709_:
{
if (v___y_712_ == 0)
{
lean_object* v___x_713_; lean_object* v_env_714_; lean_object* v_nextMacroScope_715_; lean_object* v_ngen_716_; lean_object* v_auxDeclNGen_717_; lean_object* v_traceState_718_; lean_object* v_messages_719_; lean_object* v_infoState_720_; lean_object* v_snapshotTasks_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_731_; 
v___x_713_ = lean_st_ref_take(v_a_674_);
v_env_714_ = lean_ctor_get(v___x_713_, 0);
v_nextMacroScope_715_ = lean_ctor_get(v___x_713_, 1);
v_ngen_716_ = lean_ctor_get(v___x_713_, 2);
v_auxDeclNGen_717_ = lean_ctor_get(v___x_713_, 3);
v_traceState_718_ = lean_ctor_get(v___x_713_, 4);
v_messages_719_ = lean_ctor_get(v___x_713_, 6);
v_infoState_720_ = lean_ctor_get(v___x_713_, 7);
v_snapshotTasks_721_ = lean_ctor_get(v___x_713_, 8);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v___x_713_, 5);
lean_dec(v_unused_732_);
v___x_723_ = v___x_713_;
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snapshotTasks_721_);
lean_inc(v_infoState_720_);
lean_inc(v_messages_719_);
lean_inc(v_traceState_718_);
lean_inc(v_auxDeclNGen_717_);
lean_inc(v_ngen_716_);
lean_inc(v_nextMacroScope_715_);
lean_inc(v_env_714_);
lean_dec(v___x_713_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = l_Lean_Kernel_enableDiag(v_env_714_, v___y_710_);
v___x_726_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 5, v___x_726_);
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_728_ = v___x_723_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_nextMacroScope_715_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_ngen_716_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_auxDeclNGen_717_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_traceState_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 5, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_730_, 6, v_messages_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 7, v_infoState_720_);
lean_ctor_set(v_reuseFailAlloc_730_, 8, v_snapshotTasks_721_);
v___x_728_ = v_reuseFailAlloc_730_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; 
v___x_729_ = lean_st_ref_put(v_a_674_, v___x_728_);
v___y_677_ = v___y_710_;
v___y_678_ = v___y_711_;
v_toCold_679_ = v_toCold_699_;
v_currRecDepth_680_ = v_currRecDepth_701_;
v_ref_681_ = v_ref_702_;
v_currNamespace_682_ = v_currNamespace_703_;
v_openDecls_683_ = v_openDecls_704_;
v_initHeartbeats_684_ = v_initHeartbeats_705_;
v_maxHeartbeats_685_ = v_maxHeartbeats_706_;
v_currMacroScope_686_ = v_currMacroScope_707_;
v_suppressElabErrors_687_ = v_suppressElabErrors_708_;
v___y_688_ = v_a_674_;
goto v___jp_676_;
}
}
}
else
{
v___y_677_ = v___y_710_;
v___y_678_ = v___y_711_;
v_toCold_679_ = v_toCold_699_;
v_currRecDepth_680_ = v_currRecDepth_701_;
v_ref_681_ = v_ref_702_;
v_currNamespace_682_ = v_currNamespace_703_;
v_openDecls_683_ = v_openDecls_704_;
v_initHeartbeats_684_ = v_initHeartbeats_705_;
v_maxHeartbeats_685_ = v_maxHeartbeats_706_;
v_currMacroScope_686_ = v_currMacroScope_707_;
v_suppressElabErrors_687_ = v_suppressElabErrors_708_;
v___y_688_ = v_a_674_;
goto v___jp_676_;
}
}
v___jp_733_:
{
lean_object* v_env_735_; lean_object* v___x_736_; uint8_t v___x_737_; uint8_t v___x_738_; 
v_env_735_ = lean_ctor_get(v___x_694_, 0);
lean_inc_ref(v_env_735_);
lean_dec(v___x_694_);
v___x_736_ = l_Lean_diagnostics;
v___x_737_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_734_, v___x_736_);
v___x_738_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_735_);
lean_dec_ref(v_env_735_);
if (v___x_737_ == 0)
{
if (v___x_738_ == 0)
{
v___y_677_ = v___x_737_;
v___y_678_ = v___y_734_;
v_toCold_679_ = v_toCold_699_;
v_currRecDepth_680_ = v_currRecDepth_701_;
v_ref_681_ = v_ref_702_;
v_currNamespace_682_ = v_currNamespace_703_;
v_openDecls_683_ = v_openDecls_704_;
v_initHeartbeats_684_ = v_initHeartbeats_705_;
v_maxHeartbeats_685_ = v_maxHeartbeats_706_;
v_currMacroScope_686_ = v_currMacroScope_707_;
v_suppressElabErrors_687_ = v_suppressElabErrors_708_;
v___y_688_ = v_a_674_;
goto v___jp_676_;
}
else
{
v___y_710_ = v___x_737_;
v___y_711_ = v___y_734_;
v___y_712_ = v___x_737_;
goto v___jp_709_;
}
}
else
{
v___y_710_ = v___x_737_;
v___y_711_ = v___y_734_;
v___y_712_ = v___x_738_;
goto v___jp_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_766_, lean_object* v_act_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_766_, v_act_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_774_, lean_object* v_declName_775_, lean_object* v_act_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_775_, v_act_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_783_, lean_object* v_declName_784_, lean_object* v_act_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_783_, v_declName_784_, v_act_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_env_796_; lean_object* v_toConstantVal_797_; lean_object* v_value_798_; lean_object* v_all_799_; uint8_t v___y_801_; lean_object* v_type_809_; uint8_t v___x_810_; 
v___x_795_ = lean_st_ref_get(v___y_793_);
v_env_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc_ref_n(v_env_796_, 2);
lean_dec(v___x_795_);
v_toConstantVal_797_ = lean_ctor_get(v_thm_792_, 0);
v_value_798_ = lean_ctor_get(v_thm_792_, 1);
v_all_799_ = lean_ctor_get(v_thm_792_, 2);
v_type_809_ = lean_ctor_get(v_toConstantVal_797_, 2);
v___x_810_ = l_Lean_Environment_hasUnsafe(v_env_796_, v_type_809_);
if (v___x_810_ == 0)
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_Environment_hasUnsafe(v_env_796_, v_value_798_);
v___y_801_ = v___x_811_;
goto v___jp_800_;
}
else
{
lean_dec_ref(v_env_796_);
v___y_801_ = v___x_810_;
goto v___jp_800_;
}
v___jp_800_:
{
if (v___y_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_802_, 0, v_thm_792_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_inc(v_all_799_);
lean_inc_ref(v_value_798_);
lean_inc_ref(v_toConstantVal_797_);
lean_dec_ref(v_thm_792_);
v___x_804_ = lean_box(0);
v___x_805_ = 0;
v___x_806_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_806_, 0, v_toConstantVal_797_);
lean_ctor_set(v___x_806_, 1, v_value_798_);
lean_ctor_set(v___x_806_, 2, v___x_804_);
lean_ctor_set(v___x_806_, 3, v_all_799_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*4, v___x_805_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_812_, v___y_813_);
lean_dec(v___y_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_816_, v___y_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_830_, lean_object* v_b_831_, lean_object* v_c_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
v___x_838_ = lean_apply_7(v_k_830_, v_b_831_, v_c_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, lean_box(0));
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_839_, lean_object* v_b_840_, lean_object* v_c_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_839_, v_b_840_, v_c_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_848_, lean_object* v_k_849_, uint8_t v_cleanupAnnotations_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___f_856_; uint8_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___f_856_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_856_, 0, v_k_849_);
v___x_857_ = 1;
v___x_858_ = 0;
v___x_859_ = lean_box(0);
v___x_860_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_848_, v___x_857_, v___x_858_, v___x_857_, v___x_858_, v___x_859_, v___f_856_, v_cleanupAnnotations_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_860_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_860_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_877_, lean_object* v_k_878_, lean_object* v_cleanupAnnotations_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_885_; lean_object* v_res_886_; 
v_cleanupAnnotations_boxed_885_ = lean_unbox(v_cleanupAnnotations_879_);
v_res_886_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_877_, v_k_878_, v_cleanupAnnotations_boxed_885_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_887_, lean_object* v_e_888_, lean_object* v_k_889_, uint8_t v_cleanupAnnotations_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_888_, v_k_889_, v_cleanupAnnotations_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_897_, lean_object* v_e_898_, lean_object* v_k_899_, lean_object* v_cleanupAnnotations_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_906_; lean_object* v_res_907_; 
v_cleanupAnnotations_boxed_906_ = lean_unbox(v_cleanupAnnotations_900_);
v_res_907_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_897_, v_e_898_, v_k_899_, v_cleanupAnnotations_boxed_906_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
if (lean_obj_tag(v_a_908_) == 0)
{
lean_object* v___x_910_; 
v___x_910_ = l_List_reverse___redArg(v_a_909_);
return v___x_910_;
}
else
{
lean_object* v_head_911_; lean_object* v_tail_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_921_; 
v_head_911_ = lean_ctor_get(v_a_908_, 0);
v_tail_912_ = lean_ctor_get(v_a_908_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_908_);
if (v_isSharedCheck_921_ == 0)
{
v___x_914_ = v_a_908_;
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_tail_912_);
lean_inc(v_head_911_);
lean_dec(v_a_908_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = l_Lean_mkLevelParam(v_head_911_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v_a_909_);
lean_ctor_set(v___x_914_, 0, v___x_916_);
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_a_909_);
v___x_918_ = v_reuseFailAlloc_920_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
v_a_908_ = v_tail_912_;
v_a_909_ = v___x_918_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_922_, lean_object* v_name_923_, lean_object* v_xs_924_, lean_object* v_body_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_name_931_; lean_object* v_levelParams_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_1002_; 
v_name_931_ = lean_ctor_get(v_toConstantVal_922_, 0);
v_levelParams_932_ = lean_ctor_get(v_toConstantVal_922_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_toConstantVal_922_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v_toConstantVal_922_, 2);
lean_dec(v_unused_1003_);
v___x_934_ = v_toConstantVal_922_;
v_isShared_935_ = v_isSharedCheck_1002_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_levelParams_932_);
lean_inc(v_name_931_);
lean_dec(v_toConstantVal_922_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_1002_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_lhs_939_; lean_object* v___x_940_; 
v___x_936_ = lean_box(0);
lean_inc(v_levelParams_932_);
v___x_937_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_932_, v___x_936_);
v___x_938_ = l_Lean_mkConst(v_name_931_, v___x_937_);
v_lhs_939_ = l_Lean_mkAppN(v___x_938_, v_xs_924_);
lean_inc_ref(v_lhs_939_);
v___x_940_ = l_Lean_Meta_mkEq(v_lhs_939_, v_body_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; uint8_t v___x_942_; uint8_t v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = 0;
v___x_943_ = 1;
v___x_944_ = 1;
v___x_945_ = l_Lean_Meta_mkForallFVars(v_xs_924_, v_a_941_, v___x_942_, v___x_943_, v___x_943_, v___x_944_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = l_Lean_Meta_letToHave(v_a_946_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_949_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = l_Lean_Meta_mkEqRefl(v_lhs_939_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = l_Lean_Meta_mkLambdaFVars(v_xs_924_, v_a_950_, v___x_942_, v___x_943_, v___x_942_, v___x_943_, v___x_944_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
lean_inc(v_name_923_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 2, v_a_948_);
lean_ctor_set(v___x_934_, 0, v_name_923_);
v___x_954_ = v___x_934_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_name_923_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_levelParams_932_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_a_948_);
v___x_954_ = v_reuseFailAlloc_961_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_959_; 
lean_inc(v_name_923_);
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v_name_923_);
lean_ctor_set(v___x_955_, 1, v___x_936_);
v___x_956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v_a_952_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
v___x_957_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_956_, v___y_929_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
v___x_959_ = l_Lean_addDecl(v_a_958_, v___x_942_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_960_; 
lean_dec_ref_known(v___x_959_, 1);
v___x_960_ = l_Lean_inferDefEqAttr(v_name_923_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_960_;
}
else
{
lean_dec(v_name_923_);
return v___x_959_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v_a_948_);
lean_del_object(v___x_934_);
lean_dec(v_levelParams_932_);
lean_dec(v_name_923_);
v_a_962_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_951_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_951_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec(v_a_948_);
lean_del_object(v___x_934_);
lean_dec(v_levelParams_932_);
lean_dec(v_name_923_);
v_a_970_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_949_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_949_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v_lhs_939_);
lean_del_object(v___x_934_);
lean_dec(v_levelParams_932_);
lean_dec(v_name_923_);
v_a_978_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_947_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_947_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v_lhs_939_);
lean_del_object(v___x_934_);
lean_dec(v_levelParams_932_);
lean_dec(v_name_923_);
v_a_986_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_945_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_945_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v_lhs_939_);
lean_del_object(v___x_934_);
lean_dec(v_levelParams_932_);
lean_dec(v_name_923_);
v_a_994_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_940_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_940_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1004_, lean_object* v_name_1005_, lean_object* v_xs_1006_, lean_object* v_body_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1004_, v_name_1005_, v_xs_1006_, v_body_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v_xs_1006_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1014_, lean_object* v_info_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_toConstantVal_1021_; lean_object* v_value_1022_; lean_object* v___f_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; 
v_toConstantVal_1021_ = lean_ctor_get(v_info_1015_, 0);
lean_inc_ref(v_toConstantVal_1021_);
v_value_1022_ = lean_ctor_get(v_info_1015_, 1);
lean_inc_ref(v_value_1022_);
lean_dec_ref(v_info_1015_);
v___f_1023_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1023_, 0, v_toConstantVal_1021_);
lean_closure_set(v___f_1023_, 1, v_name_1014_);
v___x_1024_ = 1;
v___x_1025_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1022_, v___f_1023_, v___x_1024_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1026_, lean_object* v_info_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1026_, v_info_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1034_, lean_object* v_name_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1044_; lean_object* v_env_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; 
v___x_1044_ = lean_st_ref_get(v_a_1039_);
v_env_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc_ref(v_env_1045_);
lean_dec(v___x_1044_);
v___x_1046_ = 0;
lean_inc(v_declName_1034_);
v___x_1047_ = l_Lean_Environment_find_x3f(v_env_1045_, v_declName_1034_, v___x_1046_);
if (lean_obj_tag(v___x_1047_) == 1)
{
lean_object* v_val_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1075_; 
v_val_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1075_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_val_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1075_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
if (lean_obj_tag(v_val_1048_) == 1)
{
lean_object* v_val_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_val_1052_ = lean_ctor_get(v_val_1048_, 0);
lean_inc_ref(v_val_1052_);
lean_dec_ref_known(v_val_1048_, 1);
lean_inc_n(v_name_1035_, 2);
v___x_1053_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1053_, 0, v_name_1035_);
lean_closure_set(v___x_1053_, 1, v_val_1052_);
lean_inc(v_declName_1034_);
v___x_1054_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1054_, 0, lean_box(0));
lean_closure_set(v___x_1054_, 1, v_declName_1034_);
lean_closure_set(v___x_1054_, 2, v___x_1053_);
v___x_1055_ = l_Lean_Meta_realizeConst(v_declName_1034_, v_name_1035_, v___x_1054_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1065_; 
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v___x_1055_, 0);
lean_dec(v_unused_1066_);
v___x_1057_ = v___x_1055_;
v_isShared_1058_ = v_isSharedCheck_1065_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v___x_1055_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1065_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v_name_1035_);
v___x_1060_ = v___x_1050_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_name_1035_);
v___x_1060_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_del_object(v___x_1050_);
lean_dec(v_name_1035_);
v_a_1067_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1055_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1055_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_del_object(v___x_1050_);
lean_dec(v_val_1048_);
lean_dec(v_name_1035_);
lean_dec(v_declName_1034_);
goto v___jp_1041_;
}
}
}
else
{
lean_dec(v___x_1047_);
lean_dec(v_name_1035_);
lean_dec(v_declName_1034_);
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1076_, lean_object* v_name_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1076_, v_name_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1084_, lean_object* v_vals_1085_, lean_object* v_i_1086_, lean_object* v_k_1087_){
_start:
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_array_get_size(v_keys_1084_);
v___x_1089_ = lean_nat_dec_lt(v_i_1086_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec(v_i_1086_);
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
else
{
lean_object* v_k_x27_1091_; uint8_t v___x_1092_; 
v_k_x27_1091_ = lean_array_fget_borrowed(v_keys_1084_, v_i_1086_);
v___x_1092_ = lean_name_eq(v_k_1087_, v_k_x27_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_i_1086_, v___x_1093_);
lean_dec(v_i_1086_);
v_i_1086_ = v___x_1094_;
goto _start;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_array_fget_borrowed(v_vals_1085_, v_i_1086_);
lean_dec(v_i_1086_);
lean_inc(v___x_1096_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1098_, lean_object* v_vals_1099_, lean_object* v_i_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1098_, v_vals_1099_, v_i_1100_, v_k_1101_);
lean_dec(v_k_1101_);
lean_dec_ref(v_vals_1099_);
lean_dec_ref(v_keys_1098_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1103_, size_t v_x_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1103_) == 0)
{
lean_object* v_es_1106_; lean_object* v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v_j_1110_; lean_object* v___x_1111_; 
v_es_1106_ = lean_ctor_get(v_x_1103_, 0);
v___x_1107_ = lean_box(2);
v___x_1108_ = ((size_t)31ULL);
v___x_1109_ = lean_usize_land(v_x_1104_, v___x_1108_);
v_j_1110_ = lean_usize_to_nat(v___x_1109_);
v___x_1111_ = lean_array_get_borrowed(v___x_1107_, v_es_1106_, v_j_1110_);
lean_dec(v_j_1110_);
switch(lean_obj_tag(v___x_1111_))
{
case 0:
{
lean_object* v_key_1112_; lean_object* v_val_1113_; uint8_t v___x_1114_; 
v_key_1112_ = lean_ctor_get(v___x_1111_, 0);
v_val_1113_ = lean_ctor_get(v___x_1111_, 1);
v___x_1114_ = lean_name_eq(v_x_1105_, v_key_1112_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_box(0);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; 
lean_inc(v_val_1113_);
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_val_1113_);
return v___x_1116_;
}
}
case 1:
{
lean_object* v_node_1117_; size_t v___x_1118_; size_t v___x_1119_; 
v_node_1117_ = lean_ctor_get(v___x_1111_, 0);
v___x_1118_ = ((size_t)5ULL);
v___x_1119_ = lean_usize_shift_right(v_x_1104_, v___x_1118_);
v_x_1103_ = v_node_1117_;
v_x_1104_ = v___x_1119_;
goto _start;
}
default: 
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_box(0);
return v___x_1121_;
}
}
}
else
{
lean_object* v_ks_1122_; lean_object* v_vs_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_ks_1122_ = lean_ctor_get(v_x_1103_, 0);
v_vs_1123_ = lean_ctor_get(v_x_1103_, 1);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1122_, v_vs_1123_, v___x_1124_, v_x_1105_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
size_t v_x_340__boxed_1129_; lean_object* v_res_1130_; 
v_x_340__boxed_1129_ = lean_unbox_usize(v_x_1127_);
lean_dec(v_x_1127_);
v_res_1130_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1126_, v_x_340__boxed_1129_, v_x_1128_);
lean_dec(v_x_1128_);
lean_dec_ref(v_x_1126_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
uint64_t v___y_1134_; 
if (lean_obj_tag(v_x_1132_) == 0)
{
uint64_t v___x_1137_; 
v___x_1137_ = 1723ULL;
v___y_1134_ = v___x_1137_;
goto v___jp_1133_;
}
else
{
uint64_t v_hash_1138_; 
v_hash_1138_ = lean_ctor_get_uint64(v_x_1132_, sizeof(void*)*2);
v___y_1134_ = v_hash_1138_;
goto v___jp_1133_;
}
v___jp_1133_:
{
size_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_uint64_to_usize(v___y_1134_);
v___x_1136_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1131_, v___x_1135_, v_x_1132_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1139_, v_x_1140_);
lean_dec(v_x_1140_);
lean_dec_ref(v_x_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v_env_1146_; lean_object* v___x_1147_; lean_object* v_asyncMode_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1145_ = lean_st_ref_get(v_a_1143_);
v_env_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc_ref(v_env_1146_);
lean_dec(v___x_1145_);
v___x_1147_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1148_ = lean_ctor_get(v___x_1147_, 2);
v___x_1149_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1150_ = lean_box(0);
v___x_1151_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1149_, v___x_1147_, v_env_1146_, v_asyncMode_1148_, v___x_1150_);
v___x_1152_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1151_, v_thmName_1142_);
lean_dec(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec(v_thmName_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1158_, v_a_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_thmName_1163_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1169_, v_x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1172_, v_x_1173_, v_x_1174_);
lean_dec(v_x_1174_);
lean_dec_ref(v_x_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1176_, lean_object* v_x_1177_, size_t v_x_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1177_, v_x_1178_, v_x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
size_t v_x_433__boxed_1185_; lean_object* v_res_1186_; 
v_x_433__boxed_1185_ = lean_unbox_usize(v_x_1183_);
lean_dec(v_x_1183_);
v_res_1186_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1181_, v_x_1182_, v_x_433__boxed_1185_, v_x_1184_);
lean_dec(v_x_1184_);
lean_dec_ref(v_x_1182_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1187_, lean_object* v_keys_1188_, lean_object* v_vals_1189_, lean_object* v_heq_1190_, lean_object* v_i_1191_, lean_object* v_k_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1188_, v_vals_1189_, v_i_1191_, v_k_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1194_, lean_object* v_keys_1195_, lean_object* v_vals_1196_, lean_object* v_heq_1197_, lean_object* v_i_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1194_, v_keys_1195_, v_vals_1196_, v_heq_1197_, v_i_1198_, v_k_1199_);
lean_dec(v_k_1199_);
lean_dec_ref(v_vals_1196_);
lean_dec_ref(v_keys_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1201_, lean_object* v_i_1202_, lean_object* v_k_1203_){
_start:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_array_get_size(v_keys_1201_);
v___x_1205_ = lean_nat_dec_lt(v_i_1202_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_dec(v_i_1202_);
return v___x_1205_;
}
else
{
lean_object* v_k_x27_1206_; uint8_t v___x_1207_; 
v_k_x27_1206_ = lean_array_fget_borrowed(v_keys_1201_, v_i_1202_);
v___x_1207_ = lean_name_eq(v_k_1203_, v_k_x27_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_add(v_i_1202_, v___x_1208_);
lean_dec(v_i_1202_);
v_i_1202_ = v___x_1209_;
goto _start;
}
else
{
lean_dec(v_i_1202_);
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1211_, lean_object* v_i_1212_, lean_object* v_k_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1211_, v_i_1212_, v_k_1213_);
lean_dec(v_k_1213_);
lean_dec_ref(v_keys_1211_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1216_, size_t v_x_1217_, lean_object* v_x_1218_){
_start:
{
if (lean_obj_tag(v_x_1216_) == 0)
{
lean_object* v_es_1219_; lean_object* v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; lean_object* v_j_1223_; lean_object* v___x_1224_; 
v_es_1219_ = lean_ctor_get(v_x_1216_, 0);
v___x_1220_ = lean_box(2);
v___x_1221_ = ((size_t)31ULL);
v___x_1222_ = lean_usize_land(v_x_1217_, v___x_1221_);
v_j_1223_ = lean_usize_to_nat(v___x_1222_);
v___x_1224_ = lean_array_get_borrowed(v___x_1220_, v_es_1219_, v_j_1223_);
lean_dec(v_j_1223_);
switch(lean_obj_tag(v___x_1224_))
{
case 0:
{
lean_object* v_key_1225_; uint8_t v___x_1226_; 
v_key_1225_ = lean_ctor_get(v___x_1224_, 0);
v___x_1226_ = lean_name_eq(v_x_1218_, v_key_1225_);
return v___x_1226_;
}
case 1:
{
lean_object* v_node_1227_; size_t v___x_1228_; size_t v___x_1229_; 
v_node_1227_ = lean_ctor_get(v___x_1224_, 0);
v___x_1228_ = ((size_t)5ULL);
v___x_1229_ = lean_usize_shift_right(v_x_1217_, v___x_1228_);
v_x_1216_ = v_node_1227_;
v_x_1217_ = v___x_1229_;
goto _start;
}
default: 
{
uint8_t v___x_1231_; 
v___x_1231_ = 0;
return v___x_1231_;
}
}
}
else
{
lean_object* v_ks_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_ks_1232_ = lean_ctor_get(v_x_1216_, 0);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1232_, v___x_1233_, v_x_1218_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
size_t v_x_324__boxed_1238_; uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_x_324__boxed_1238_ = lean_unbox_usize(v_x_1236_);
lean_dec(v_x_1236_);
v_res_1239_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1235_, v_x_324__boxed_1238_, v_x_1237_);
lean_dec(v_x_1237_);
lean_dec_ref(v_x_1235_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
uint64_t v___y_1244_; 
if (lean_obj_tag(v_x_1242_) == 0)
{
uint64_t v___x_1247_; 
v___x_1247_ = 1723ULL;
v___y_1244_ = v___x_1247_;
goto v___jp_1243_;
}
else
{
uint64_t v_hash_1248_; 
v_hash_1248_ = lean_ctor_get_uint64(v_x_1242_, sizeof(void*)*2);
v___y_1244_ = v_hash_1248_;
goto v___jp_1243_;
}
v___jp_1243_:
{
size_t v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_uint64_to_usize(v___y_1244_);
v___x_1246_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1241_, v___x_1245_, v_x_1242_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1249_, v_x_1250_);
lean_dec(v_x_1250_);
lean_dec_ref(v_x_1249_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1256_; lean_object* v_env_1257_; lean_object* v___x_1258_; lean_object* v_asyncMode_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1256_ = lean_st_ref_get(v_a_1254_);
v_env_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc_ref(v_env_1257_);
lean_dec(v___x_1256_);
v___x_1258_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1259_ = lean_ctor_get(v___x_1258_, 2);
v___x_1260_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1261_ = lean_box(0);
v___x_1262_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1260_, v___x_1258_, v_env_1257_, v_asyncMode_1259_, v___x_1261_);
v___x_1263_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1262_, v_thmName_1253_);
lean_dec(v___x_1262_);
v___x_1264_ = lean_box(v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec(v_thmName_1266_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1270_, v_a_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Meta_isEqnThm(v_thmName_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_thmName_1275_);
return v_res_1279_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
uint8_t v___x_1283_; 
v___x_1283_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1281_, v_x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1284_, v_x_1285_, v_x_1286_);
lean_dec(v_x_1286_);
lean_dec_ref(v_x_1285_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, size_t v_x_1291_, lean_object* v_x_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1290_, v_x_1291_, v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
size_t v_x_413__boxed_1298_; uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_x_413__boxed_1298_ = lean_unbox_usize(v_x_1296_);
lean_dec(v_x_1296_);
v_res_1299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1294_, v_x_1295_, v_x_413__boxed_1298_, v_x_1297_);
lean_dec(v_x_1297_);
lean_dec_ref(v_x_1295_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1301_, lean_object* v_keys_1302_, lean_object* v_vals_1303_, lean_object* v_heq_1304_, lean_object* v_i_1305_, lean_object* v_k_1306_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1302_, v_i_1305_, v_k_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1308_, lean_object* v_keys_1309_, lean_object* v_vals_1310_, lean_object* v_heq_1311_, lean_object* v_i_1312_, lean_object* v_k_1313_){
_start:
{
uint8_t v_res_1314_; lean_object* v_r_1315_; 
v_res_1314_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1308_, v_keys_1309_, v_vals_1310_, v_heq_1311_, v_i_1312_, v_k_1313_);
lean_dec(v_k_1313_);
lean_dec_ref(v_vals_1310_);
lean_dec_ref(v_keys_1309_);
v_r_1315_ = lean_box(v_res_1314_);
return v_r_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
lean_object* v_ks_1320_; lean_object* v_vs_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1345_; 
v_ks_1320_ = lean_ctor_get(v_x_1316_, 0);
v_vs_1321_ = lean_ctor_get(v_x_1316_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_x_1316_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1323_ = v_x_1316_;
v_isShared_1324_ = v_isSharedCheck_1345_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_vs_1321_);
lean_inc(v_ks_1320_);
lean_dec(v_x_1316_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1345_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_array_get_size(v_ks_1320_);
v___x_1326_ = lean_nat_dec_lt(v_x_1317_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
lean_dec(v_x_1317_);
v___x_1327_ = lean_array_push(v_ks_1320_, v_x_1318_);
v___x_1328_ = lean_array_push(v_vs_1321_, v_x_1319_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v___x_1328_);
lean_ctor_set(v___x_1323_, 0, v___x_1327_);
v___x_1330_ = v___x_1323_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
else
{
lean_object* v_k_x27_1332_; uint8_t v___x_1333_; 
v_k_x27_1332_ = lean_array_fget_borrowed(v_ks_1320_, v_x_1317_);
v___x_1333_ = lean_name_eq(v_x_1318_, v_k_x27_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1335_; 
if (v_isShared_1324_ == 0)
{
v___x_1335_ = v___x_1323_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_ks_1320_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_vs_1321_);
v___x_1335_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v_x_1317_, v___x_1336_);
lean_dec(v_x_1317_);
v_x_1316_ = v___x_1335_;
v_x_1317_ = v___x_1337_;
goto _start;
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1340_ = lean_array_fset(v_ks_1320_, v_x_1317_, v_x_1318_);
v___x_1341_ = lean_array_fset(v_vs_1321_, v_x_1317_, v_x_1319_);
lean_dec(v_x_1317_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v___x_1341_);
lean_ctor_set(v___x_1323_, 0, v___x_1340_);
v___x_1343_ = v___x_1323_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1346_, lean_object* v_k_1347_, lean_object* v_v_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1346_, v___x_1349_, v_k_1347_, v_v_1348_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1352_, size_t v_x_1353_, size_t v_x_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1352_) == 0)
{
lean_object* v_es_1357_; size_t v___x_1358_; size_t v___x_1359_; lean_object* v_j_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_es_1357_ = lean_ctor_get(v_x_1352_, 0);
v___x_1358_ = ((size_t)31ULL);
v___x_1359_ = lean_usize_land(v_x_1353_, v___x_1358_);
v_j_1360_ = lean_usize_to_nat(v___x_1359_);
v___x_1361_ = lean_array_get_size(v_es_1357_);
v___x_1362_ = lean_nat_dec_lt(v_j_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_dec(v_j_1360_);
lean_dec(v_x_1356_);
lean_dec(v_x_1355_);
return v_x_1352_;
}
else
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1401_; 
lean_inc_ref(v_es_1357_);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v_x_1352_, 0);
lean_dec(v_unused_1402_);
v___x_1364_ = v_x_1352_;
v_isShared_1365_ = v_isSharedCheck_1401_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v_x_1352_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1401_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_v_1366_; lean_object* v___x_1367_; lean_object* v_xs_x27_1368_; lean_object* v___y_1370_; 
v_v_1366_ = lean_array_fget(v_es_1357_, v_j_1360_);
v___x_1367_ = lean_box(0);
v_xs_x27_1368_ = lean_array_fset(v_es_1357_, v_j_1360_, v___x_1367_);
switch(lean_obj_tag(v_v_1366_))
{
case 0:
{
lean_object* v_key_1375_; lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1386_; 
v_key_1375_ = lean_ctor_get(v_v_1366_, 0);
v_val_1376_ = lean_ctor_get(v_v_1366_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_v_1366_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1378_ = v_v_1366_;
v_isShared_1379_ = v_isSharedCheck_1386_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_inc(v_key_1375_);
lean_dec(v_v_1366_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1386_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_name_eq(v_x_1355_, v_key_1375_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_del_object(v___x_1378_);
v___x_1381_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1375_, v_val_1376_, v_x_1355_, v_x_1356_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___y_1370_ = v___x_1382_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1384_; 
lean_dec(v_val_1376_);
lean_dec(v_key_1375_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v_x_1356_);
lean_ctor_set(v___x_1378_, 0, v_x_1355_);
v___x_1384_ = v___x_1378_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_x_1355_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_x_1356_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
v___y_1370_ = v___x_1384_;
goto v___jp_1369_;
}
}
}
}
case 1:
{
lean_object* v_node_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1399_; 
v_node_1387_ = lean_ctor_get(v_v_1366_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_v_1366_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1389_ = v_v_1366_;
v_isShared_1390_ = v_isSharedCheck_1399_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_node_1387_);
lean_dec(v_v_1366_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1399_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
size_t v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1391_ = ((size_t)5ULL);
v___x_1392_ = lean_usize_shift_right(v_x_1353_, v___x_1391_);
v___x_1393_ = ((size_t)1ULL);
v___x_1394_ = lean_usize_add(v_x_1354_, v___x_1393_);
v___x_1395_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1387_, v___x_1392_, v___x_1394_, v_x_1355_, v_x_1356_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1395_);
v___x_1397_ = v___x_1389_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
v___y_1370_ = v___x_1397_;
goto v___jp_1369_;
}
}
}
default: 
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_x_1355_);
lean_ctor_set(v___x_1400_, 1, v_x_1356_);
v___y_1370_ = v___x_1400_;
goto v___jp_1369_;
}
}
v___jp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_array_fset(v_xs_x27_1368_, v_j_1360_, v___y_1370_);
lean_dec(v_j_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1371_);
v___x_1373_ = v___x_1364_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
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
else
{
lean_object* v_ks_1403_; lean_object* v_vs_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1422_; 
v_ks_1403_ = lean_ctor_get(v_x_1352_, 0);
v_vs_1404_ = lean_ctor_get(v_x_1352_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1406_ = v_x_1352_;
v_isShared_1407_ = v_isSharedCheck_1422_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_vs_1404_);
lean_inc(v_ks_1403_);
lean_dec(v_x_1352_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1422_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_ks_1403_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_vs_1404_);
v___x_1409_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v_newNode_1410_; size_t v___x_1411_; uint8_t v___x_1412_; 
v_newNode_1410_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1409_, v_x_1355_, v_x_1356_);
v___x_1411_ = ((size_t)7ULL);
v___x_1412_ = lean_usize_dec_le(v___x_1411_, v_x_1354_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1410_);
v___x_1414_ = lean_unsigned_to_nat(4u);
v___x_1415_ = lean_nat_dec_lt(v___x_1413_, v___x_1414_);
lean_dec(v___x_1413_);
if (v___x_1415_ == 0)
{
lean_object* v_ks_1416_; lean_object* v_vs_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_ks_1416_ = lean_ctor_get(v_newNode_1410_, 0);
lean_inc_ref(v_ks_1416_);
v_vs_1417_ = lean_ctor_get(v_newNode_1410_, 1);
lean_inc_ref(v_vs_1417_);
lean_dec_ref(v_newNode_1410_);
v___x_1418_ = lean_unsigned_to_nat(0u);
v___x_1419_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1420_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1354_, v_ks_1416_, v_vs_1417_, v___x_1418_, v___x_1419_);
lean_dec_ref(v_vs_1417_);
lean_dec_ref(v_ks_1416_);
return v___x_1420_;
}
else
{
return v_newNode_1410_;
}
}
else
{
return v_newNode_1410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(size_t v_depth_1423_, lean_object* v_keys_1424_, lean_object* v_vals_1425_, lean_object* v_i_1426_, lean_object* v_entries_1427_){
_start:
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_array_get_size(v_keys_1424_);
v___x_1429_ = lean_nat_dec_lt(v_i_1426_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_dec(v_i_1426_);
return v_entries_1427_;
}
else
{
lean_object* v_k_1430_; lean_object* v_v_1431_; uint64_t v___y_1433_; 
v_k_1430_ = lean_array_fget_borrowed(v_keys_1424_, v_i_1426_);
v_v_1431_ = lean_array_fget_borrowed(v_vals_1425_, v_i_1426_);
if (lean_obj_tag(v_k_1430_) == 0)
{
uint64_t v___x_1444_; 
v___x_1444_ = 1723ULL;
v___y_1433_ = v___x_1444_;
goto v___jp_1432_;
}
else
{
uint64_t v_hash_1445_; 
v_hash_1445_ = lean_ctor_get_uint64(v_k_1430_, sizeof(void*)*2);
v___y_1433_ = v_hash_1445_;
goto v___jp_1432_;
}
v___jp_1432_:
{
size_t v_h_1434_; size_t v___x_1435_; lean_object* v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; size_t v_h_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_h_1434_ = lean_uint64_to_usize(v___y_1433_);
v___x_1435_ = ((size_t)5ULL);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = ((size_t)1ULL);
v___x_1438_ = lean_usize_sub(v_depth_1423_, v___x_1437_);
v___x_1439_ = lean_usize_mul(v___x_1435_, v___x_1438_);
v_h_1440_ = lean_usize_shift_right(v_h_1434_, v___x_1439_);
v___x_1441_ = lean_nat_add(v_i_1426_, v___x_1436_);
lean_dec(v_i_1426_);
lean_inc(v_v_1431_);
lean_inc(v_k_1430_);
v___x_1442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_1427_, v_h_1440_, v_depth_1423_, v_k_1430_, v_v_1431_);
v_i_1426_ = v___x_1441_;
v_entries_1427_ = v___x_1442_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1446_, lean_object* v_keys_1447_, lean_object* v_vals_1448_, lean_object* v_i_1449_, lean_object* v_entries_1450_){
_start:
{
size_t v_depth_boxed_1451_; lean_object* v_res_1452_; 
v_depth_boxed_1451_ = lean_unbox_usize(v_depth_1446_);
lean_dec(v_depth_1446_);
v_res_1452_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1451_, v_keys_1447_, v_vals_1448_, v_i_1449_, v_entries_1450_);
lean_dec_ref(v_vals_1448_);
lean_dec_ref(v_keys_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
size_t v_x_625__boxed_1458_; size_t v_x_626__boxed_1459_; lean_object* v_res_1460_; 
v_x_625__boxed_1458_ = lean_unbox_usize(v_x_1454_);
lean_dec(v_x_1454_);
v_x_626__boxed_1459_ = lean_unbox_usize(v_x_1455_);
lean_dec(v_x_1455_);
v_res_1460_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1453_, v_x_625__boxed_1458_, v_x_626__boxed_1459_, v_x_1456_, v_x_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
uint64_t v___y_1465_; 
if (lean_obj_tag(v_x_1462_) == 0)
{
uint64_t v___x_1469_; 
v___x_1469_ = 1723ULL;
v___y_1465_ = v___x_1469_;
goto v___jp_1464_;
}
else
{
uint64_t v_hash_1470_; 
v_hash_1470_ = lean_ctor_get_uint64(v_x_1462_, sizeof(void*)*2);
v___y_1465_ = v_hash_1470_;
goto v___jp_1464_;
}
v___jp_1464_:
{
size_t v___x_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = lean_uint64_to_usize(v___y_1465_);
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1461_, v___x_1466_, v___x_1467_, v_x_1462_, v_x_1463_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(lean_object* v_declName_1471_, lean_object* v_as_1472_, size_t v_i_1473_, size_t v_stop_1474_, lean_object* v_b_1475_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_eq(v_i_1473_, v_stop_1474_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; 
v___x_1477_ = lean_array_uget_borrowed(v_as_1472_, v_i_1473_);
lean_inc(v_declName_1471_);
lean_inc(v___x_1477_);
v___x_1478_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_1475_, v___x_1477_, v_declName_1471_);
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1473_, v___x_1479_);
v_i_1473_ = v___x_1480_;
v_b_1475_ = v___x_1478_;
goto _start;
}
else
{
lean_dec(v_declName_1471_);
return v_b_1475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(lean_object* v_declName_1482_, lean_object* v_as_1483_, lean_object* v_i_1484_, lean_object* v_stop_1485_, lean_object* v_b_1486_){
_start:
{
size_t v_i_boxed_1487_; size_t v_stop_boxed_1488_; lean_object* v_res_1489_; 
v_i_boxed_1487_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_stop_boxed_1488_ = lean_unbox_usize(v_stop_1485_);
lean_dec(v_stop_1485_);
v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1482_, v_as_1483_, v_i_boxed_1487_, v_stop_boxed_1488_, v_b_1486_);
lean_dec_ref(v_as_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* v_eqThms_1490_, lean_object* v_declName_1491_, lean_object* v_s_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = lean_array_get_size(v_eqThms_1490_);
v___x_1495_ = lean_nat_dec_lt(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_dec(v_declName_1491_);
return v_s_1492_;
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_le(v___x_1494_, v___x_1494_);
if (v___x_1496_ == 0)
{
if (v___x_1495_ == 0)
{
lean_dec(v_declName_1491_);
return v_s_1492_;
}
else
{
size_t v___x_1497_; size_t v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = ((size_t)0ULL);
v___x_1498_ = lean_usize_of_nat(v___x_1494_);
v___x_1499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1491_, v_eqThms_1490_, v___x_1497_, v___x_1498_, v_s_1492_);
return v___x_1499_;
}
}
else
{
size_t v___x_1500_; size_t v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = ((size_t)0ULL);
v___x_1501_ = lean_usize_of_nat(v___x_1494_);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_1491_, v_eqThms_1490_, v___x_1500_, v___x_1501_, v_s_1492_);
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* v_eqThms_1503_, lean_object* v_declName_1504_, lean_object* v_s_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(v_eqThms_1503_, v_declName_1504_, v_s_1505_);
lean_dec_ref(v_eqThms_1503_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* v_declName_1507_, lean_object* v_eqThms_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v_env_1512_; lean_object* v_nextMacroScope_1513_; lean_object* v_ngen_1514_; lean_object* v_auxDeclNGen_1515_; lean_object* v_traceState_1516_; lean_object* v_messages_1517_; lean_object* v_infoState_1518_; lean_object* v_snapshotTasks_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1535_; 
v___x_1511_ = lean_st_ref_take(v_a_1509_);
v_env_1512_ = lean_ctor_get(v___x_1511_, 0);
v_nextMacroScope_1513_ = lean_ctor_get(v___x_1511_, 1);
v_ngen_1514_ = lean_ctor_get(v___x_1511_, 2);
v_auxDeclNGen_1515_ = lean_ctor_get(v___x_1511_, 3);
v_traceState_1516_ = lean_ctor_get(v___x_1511_, 4);
v_messages_1517_ = lean_ctor_get(v___x_1511_, 6);
v_infoState_1518_ = lean_ctor_get(v___x_1511_, 7);
v_snapshotTasks_1519_ = lean_ctor_get(v___x_1511_, 8);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v___x_1511_, 5);
lean_dec(v_unused_1536_);
v___x_1521_ = v___x_1511_;
v_isShared_1522_ = v_isSharedCheck_1535_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snapshotTasks_1519_);
lean_inc(v_infoState_1518_);
lean_inc(v_messages_1517_);
lean_inc(v_traceState_1516_);
lean_inc(v_auxDeclNGen_1515_);
lean_inc(v_ngen_1514_);
lean_inc(v_nextMacroScope_1513_);
lean_inc(v_env_1512_);
lean_dec(v___x_1511_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1535_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v_asyncMode_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1523_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1524_ = lean_ctor_get(v___x_1523_, 2);
v___f_1525_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1525_, 0, v_eqThms_1508_);
lean_closure_set(v___f_1525_, 1, v_declName_1507_);
v___x_1526_ = lean_box(0);
v___x_1527_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1523_, v_env_1512_, v___f_1525_, v_asyncMode_1524_, v___x_1526_);
v___x_1528_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 5, v___x_1528_);
lean_ctor_set(v___x_1521_, 0, v___x_1527_);
v___x_1530_ = v___x_1521_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_nextMacroScope_1513_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_ngen_1514_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_auxDeclNGen_1515_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_traceState_1516_);
lean_ctor_set(v_reuseFailAlloc_1534_, 5, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1534_, 6, v_messages_1517_);
lean_ctor_set(v_reuseFailAlloc_1534_, 7, v_infoState_1518_);
lean_ctor_set(v_reuseFailAlloc_1534_, 8, v_snapshotTasks_1519_);
v___x_1530_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_st_ref_put(v_a_1509_, v___x_1530_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* v_declName_1537_, lean_object* v_eqThms_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1537_, v_eqThms_1538_, v_a_1539_);
lean_dec(v_a_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* v_declName_1542_, lean_object* v_eqThms_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1542_, v_eqThms_1543_, v_a_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* v_declName_1548_, lean_object* v_eqThms_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(v_declName_1548_, v_eqThms_1549_, v_a_1550_, v_a_1551_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* v_00_u03b2_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_, lean_object* v_x_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_1555_, v_x_1556_, v_x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(lean_object* v_00_u03b2_1559_, lean_object* v_x_1560_, size_t v_x_1561_, size_t v_x_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1560_, v_x_1561_, v_x_1562_, v_x_1563_, v_x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_, lean_object* v_x_1571_){
_start:
{
size_t v_x_887__boxed_1572_; size_t v_x_888__boxed_1573_; lean_object* v_res_1574_; 
v_x_887__boxed_1572_ = lean_unbox_usize(v_x_1568_);
lean_dec(v_x_1568_);
v_x_888__boxed_1573_ = lean_unbox_usize(v_x_1569_);
lean_dec(v_x_1569_);
v_res_1574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1566_, v_x_1567_, v_x_887__boxed_1572_, v_x_888__boxed_1573_, v_x_1570_, v_x_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1575_, lean_object* v_n_1576_, lean_object* v_k_1577_, lean_object* v_v_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_1576_, v_k_1577_, v_v_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1580_, size_t v_depth_1581_, lean_object* v_keys_1582_, lean_object* v_vals_1583_, lean_object* v_heq_1584_, lean_object* v_i_1585_, lean_object* v_entries_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_1581_, v_keys_1582_, v_vals_1583_, v_i_1585_, v_entries_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1588_, lean_object* v_depth_1589_, lean_object* v_keys_1590_, lean_object* v_vals_1591_, lean_object* v_heq_1592_, lean_object* v_i_1593_, lean_object* v_entries_1594_){
_start:
{
size_t v_depth_boxed_1595_; lean_object* v_res_1596_; 
v_depth_boxed_1595_ = lean_unbox_usize(v_depth_1589_);
lean_dec(v_depth_1589_);
v_res_1596_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_1588_, v_depth_boxed_1595_, v_keys_1590_, v_vals_1591_, v_heq_1592_, v_i_1593_, v_entries_1594_);
lean_dec_ref(v_vals_1591_);
lean_dec_ref(v_keys_1590_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1597_, lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1598_, v_x_1599_, v_x_1600_, v_x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* v_declName_1603_, lean_object* v_env_1604_, lean_object* v_idx_1605_, lean_object* v_eqs_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_nextEq_1613_; uint8_t v___x_1614_; 
v___x_1608_ = ((lean_object*)(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0));
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_add(v_idx_1605_, v___x_1609_);
lean_dec(v_idx_1605_);
lean_inc(v___x_1610_);
v___x_1611_ = l_Nat_reprFast(v___x_1610_);
v___x_1612_ = lean_string_append(v___x_1608_, v___x_1611_);
lean_dec_ref(v___x_1611_);
lean_inc(v_declName_1603_);
lean_inc_ref(v_env_1604_);
v_nextEq_1613_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1604_, v_declName_1603_, v___x_1612_);
v___x_1614_ = l_Lean_Environment_containsOnBranch(v_env_1604_, v_nextEq_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_dec(v_nextEq_1613_);
lean_dec(v___x_1610_);
lean_dec_ref(v_env_1604_);
lean_dec(v_declName_1603_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_eqs_1606_);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_array_push(v_eqs_1606_, v_nextEq_1613_);
v_idx_1605_ = v___x_1610_;
v_eqs_1606_ = v___x_1616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(lean_object* v_declName_1618_, lean_object* v_env_1619_, lean_object* v_idx_1620_, lean_object* v_eqs_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1618_, v_env_1619_, v_idx_1620_, v_eqs_1621_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* v_declName_1624_, lean_object* v_env_1625_, lean_object* v_idx_1626_, lean_object* v_eqs_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1624_, v_env_1625_, v_idx_1626_, v_eqs_1627_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* v_declName_1634_, lean_object* v_env_1635_, lean_object* v_idx_1636_, lean_object* v_eqs_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(v_declName_1634_, v_env_1635_, v_idx_1636_, v_eqs_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* v_declName_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v___x_1647_; lean_object* v_env_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; uint8_t v___x_1652_; 
v___x_1647_ = lean_st_ref_get(v_a_1645_);
v_env_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc_ref_n(v_env_1648_, 3);
lean_dec(v___x_1647_);
v___x_1649_ = ((lean_object*)(l_Lean_Meta_eqn1ThmSuffix___closed__0));
lean_inc(v_declName_1644_);
v___x_1650_ = l_Lean_Meta_mkEqLikeNameFor(v_env_1648_, v_declName_1644_, v___x_1649_);
v___x_1651_ = 1;
lean_inc(v___x_1650_);
v___x_1652_ = l_Lean_Environment_contains(v_env_1648_, v___x_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec(v___x_1650_);
lean_dec_ref(v_env_1648_);
lean_dec(v_declName_1644_);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1655_ = lean_unsigned_to_nat(1u);
v___x_1656_ = lean_mk_empty_array_with_capacity(v___x_1655_);
v___x_1657_ = lean_array_push(v___x_1656_, v___x_1650_);
lean_inc(v_declName_1644_);
v___x_1658_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(v_declName_1644_, v_env_1648_, v___x_1655_, v___x_1657_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc_n(v_a_1659_, 2);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1644_, v_a_1659_, v_a_1645_);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v___x_1660_, 0);
lean_dec(v_unused_1669_);
v___x_1662_ = v___x_1660_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v___x_1660_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_a_1659_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1664_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_declName_1644_);
v_a_1670_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1658_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1658_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* v_declName_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1678_, v_a_1679_);
lean_dec(v_a_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* v_declName_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1682_, v_a_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* v_declName_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(v_declName_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(lean_object* v_lctx_1696_, lean_object* v_localInsts_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1696_, v_localInsts_1697_, v_x_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1713_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1704_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1704_);
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
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(lean_object* v_lctx_1721_, lean_object* v_localInsts_1722_, lean_object* v_x_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1721_, v_localInsts_1722_, v_x_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(lean_object* v_00_u03b1_1730_, lean_object* v_lctx_1731_, lean_object* v_localInsts_1732_, lean_object* v_x_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_1731_, v_localInsts_1732_, v_x_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(lean_object* v_00_u03b1_1740_, lean_object* v_lctx_1741_, lean_object* v_localInsts_1742_, lean_object* v_x_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_1740_, v_lctx_1741_, v_localInsts_1742_, v_x_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* v_declName_1753_, lean_object* v_as_x27_1754_, lean_object* v_b_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
if (lean_obj_tag(v_as_x27_1754_) == 0)
{
lean_object* v___x_1761_; 
lean_dec(v_declName_1753_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_b_1755_);
return v___x_1761_;
}
else
{
lean_object* v_head_1762_; lean_object* v_tail_1763_; lean_object* v___x_1764_; 
lean_dec_ref(v_b_1755_);
v_head_1762_ = lean_ctor_get(v_as_x27_1754_, 0);
v_tail_1763_ = lean_ctor_get(v_as_x27_1754_, 1);
lean_inc(v_head_1762_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
lean_inc(v___y_1757_);
lean_inc_ref(v___y_1756_);
lean_inc(v_declName_1753_);
v___x_1764_ = lean_apply_6(v_head_1762_, v_declName_1753_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, lean_box(0));
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = lean_box(0);
if (lean_obj_tag(v_a_1765_) == 1)
{
lean_object* v_val_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1777_; 
v_val_1767_ = lean_ctor_get(v_a_1765_, 0);
lean_inc(v_val_1767_);
v___x_1768_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(v_declName_1753_, v_val_1767_, v___y_1759_);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v___x_1768_, 0);
lean_dec(v_unused_1778_);
v___x_1770_ = v___x_1768_;
v_isShared_1771_ = v_isSharedCheck_1777_;
goto v_resetjp_1769_;
}
else
{
lean_dec(v___x_1768_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1777_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_a_1765_);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___x_1766_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1773_);
v___x_1775_ = v___x_1770_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
else
{
lean_object* v___x_1779_; 
lean_dec(v_a_1765_);
v___x_1779_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v_as_x27_1754_ = v_tail_1763_;
v_b_1755_ = v___x_1779_;
goto _start;
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_declName_1753_);
v_a_1781_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1764_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1764_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(lean_object* v_declName_1789_, lean_object* v_as_x27_1790_, lean_object* v_b_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1789_, v_as_x27_1790_, v_b_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v_as_x27_1790_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* v_declName_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
lean_inc(v_declName_1798_);
v___x_1804_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1842_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1842_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1842_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_unbox(v_a_1805_);
lean_dec(v_a_1805_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
lean_dec(v_declName_1798_);
v___x_1810_ = lean_box(0);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1810_);
v___x_1812_ = v___x_1807_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
else
{
lean_object* v___x_1814_; 
lean_del_object(v___x_1807_);
lean_inc(v_declName_1798_);
v___x_1814_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(v_declName_1798_, v___y_1802_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
if (lean_obj_tag(v_a_1815_) == 1)
{
lean_dec_ref_known(v_a_1815_, 1);
lean_dec(v_declName_1798_);
return v___x_1814_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref_known(v___x_1814_, 1);
lean_dec(v_a_1815_);
v___x_1816_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
v___x_1817_ = lean_st_ref_get(v___x_1816_);
v___x_1818_ = lean_box(0);
v___x_1819_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0));
v___x_1820_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1798_, v___x_1817_, v___x_1819_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___x_1817_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1833_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1833_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1833_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_fst_1825_; 
v_fst_1825_ = lean_ctor_get(v_a_1821_, 0);
lean_inc(v_fst_1825_);
lean_dec(v_a_1821_);
if (lean_obj_tag(v_fst_1825_) == 0)
{
lean_object* v___x_1827_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1818_);
v___x_1827_ = v___x_1823_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1818_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
else
{
lean_object* v_val_1829_; lean_object* v___x_1831_; 
v_val_1829_ = lean_ctor_get(v_fst_1825_, 0);
lean_inc(v_val_1829_);
lean_dec_ref_known(v_fst_1825_, 1);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v_val_1829_);
v___x_1831_ = v___x_1823_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_val_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
v_a_1834_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1820_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1820_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
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
}
else
{
lean_dec(v_declName_1798_);
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_declName_1798_);
v_a_1843_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1804_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1804_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(lean_object* v_declName_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(v_declName_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0(void){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1858_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1861_ = lean_box(1);
v___x_1862_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_1863_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_1864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v___x_1862_);
lean_ctor_set(v___x_1864_, 2, v___x_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* v_declName_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___f_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___f_1873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1873_, 0, v_declName_1867_);
v___x_1874_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_1876_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1874_, v___x_1875_, v___f_1873_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(lean_object* v_declName_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(v_declName_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* v_declName_1884_, lean_object* v_as_1885_, lean_object* v_as_x27_1886_, lean_object* v_b_1887_, lean_object* v_a_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_1884_, v_as_x27_1886_, v_b_1887_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* v_declName_1895_, lean_object* v_as_1896_, lean_object* v_as_x27_1897_, lean_object* v_b_1898_, lean_object* v_a_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_1895_, v_as_1896_, v_as_x27_1897_, v_b_1898_, v_a_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v_as_x27_1897_);
lean_dec(v_as_1896_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* v_declName_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1912_ = lean_unsigned_to_nat(32u);
v___x_1913_ = lean_mk_empty_array_with_capacity(v___x_1912_);
lean_dec_ref(v___x_1913_);
v___x_1914_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
lean_inc(v_declName_1906_);
v___x_1916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed), 6, 1);
lean_closure_set(v___x_1916_, 0, v_declName_1906_);
v___x_1917_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1917_, 0, lean_box(0));
lean_closure_set(v___x_1917_, 1, v_declName_1906_);
lean_closure_set(v___x_1917_, 2, v___x_1916_);
v___x_1918_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_1914_, v___x_1915_, v___x_1917_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___boxed(lean_object* v_declName_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(lean_object* v_msgData_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v_env_1933_; lean_object* v___x_1934_; lean_object* v_mctx_1935_; lean_object* v_lctx_1936_; lean_object* v_options_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1932_ = lean_st_ref_get(v___y_1930_);
v_env_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc_ref(v_env_1933_);
lean_dec(v___x_1932_);
v___x_1934_ = lean_st_ref_get(v___y_1928_);
v_mctx_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc_ref(v_mctx_1935_);
lean_dec(v___x_1934_);
v_lctx_1936_ = lean_ctor_get(v___y_1927_, 2);
v_options_1937_ = lean_ctor_get(v___y_1929_, 1);
lean_inc_ref(v_options_1937_);
lean_inc_ref(v_lctx_1936_);
v___x_1938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1938_, 0, v_env_1933_);
lean_ctor_set(v___x_1938_, 1, v_mctx_1935_);
lean_ctor_set(v___x_1938_, 2, v_lctx_1936_);
lean_ctor_set(v___x_1938_, 3, v_options_1937_);
v___x_1939_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v_msgData_1926_);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(lean_object* v_msgData_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1947_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1948_; double v___x_1949_; 
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_float_of_nat(v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(lean_object* v_cls_1953_, lean_object* v_msg_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_ref_1960_; lean_object* v___x_1961_; lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2006_; 
v_ref_1960_ = lean_ctor_get(v___y_1957_, 4);
v___x_1961_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_2006_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2006_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v_traceState_1967_; lean_object* v_env_1968_; lean_object* v_nextMacroScope_1969_; lean_object* v_ngen_1970_; lean_object* v_auxDeclNGen_1971_; lean_object* v_cache_1972_; lean_object* v_messages_1973_; lean_object* v_infoState_1974_; lean_object* v_snapshotTasks_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2005_; 
v___x_1966_ = lean_st_ref_take(v___y_1958_);
v_traceState_1967_ = lean_ctor_get(v___x_1966_, 4);
v_env_1968_ = lean_ctor_get(v___x_1966_, 0);
v_nextMacroScope_1969_ = lean_ctor_get(v___x_1966_, 1);
v_ngen_1970_ = lean_ctor_get(v___x_1966_, 2);
v_auxDeclNGen_1971_ = lean_ctor_get(v___x_1966_, 3);
v_cache_1972_ = lean_ctor_get(v___x_1966_, 5);
v_messages_1973_ = lean_ctor_get(v___x_1966_, 6);
v_infoState_1974_ = lean_ctor_get(v___x_1966_, 7);
v_snapshotTasks_1975_ = lean_ctor_get(v___x_1966_, 8);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1977_ = v___x_1966_;
v_isShared_1978_ = v_isSharedCheck_2005_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_snapshotTasks_1975_);
lean_inc(v_infoState_1974_);
lean_inc(v_messages_1973_);
lean_inc(v_cache_1972_);
lean_inc(v_traceState_1967_);
lean_inc(v_auxDeclNGen_1971_);
lean_inc(v_ngen_1970_);
lean_inc(v_nextMacroScope_1969_);
lean_inc(v_env_1968_);
lean_dec(v___x_1966_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2005_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint64_t v_tid_1979_; lean_object* v_traces_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2004_; 
v_tid_1979_ = lean_ctor_get_uint64(v_traceState_1967_, sizeof(void*)*1);
v_traces_1980_ = lean_ctor_get(v_traceState_1967_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_traceState_1967_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1982_ = v_traceState_1967_;
v_isShared_1983_ = v_isSharedCheck_2004_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_traces_1980_);
lean_dec(v_traceState_1967_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2004_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; double v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
v___x_1986_ = 0;
v___x_1987_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_1988_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1988_, 0, v_cls_1953_);
lean_ctor_set(v___x_1988_, 1, v___x_1984_);
lean_ctor_set(v___x_1988_, 2, v___x_1987_);
lean_ctor_set_float(v___x_1988_, sizeof(void*)*3, v___x_1985_);
lean_ctor_set_float(v___x_1988_, sizeof(void*)*3 + 8, v___x_1985_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*3 + 16, v___x_1986_);
v___x_1989_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2));
v___x_1990_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v_a_1962_);
lean_ctor_set(v___x_1990_, 2, v___x_1989_);
lean_inc(v_ref_1960_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v_ref_1960_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = l_Lean_PersistentArray_push___redArg(v_traces_1980_, v___x_1991_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1992_);
v___x_1994_ = v___x_1982_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1992_);
lean_ctor_set_uint64(v_reuseFailAlloc_2003_, sizeof(void*)*1, v_tid_1979_);
v___x_1994_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 4, v___x_1994_);
v___x_1996_ = v___x_1977_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_env_1968_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_nextMacroScope_1969_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_ngen_1970_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_auxDeclNGen_1971_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2002_, 5, v_cache_1972_);
lean_ctor_set(v_reuseFailAlloc_2002_, 6, v_messages_1973_);
lean_ctor_set(v_reuseFailAlloc_2002_, 7, v_infoState_1974_);
lean_ctor_set(v_reuseFailAlloc_2002_, 8, v_snapshotTasks_1975_);
v___x_1996_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1997_ = lean_st_ref_put(v___y_1958_, v___x_1996_);
v___x_1998_ = lean_box(0);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1998_);
v___x_2000_ = v___x_1964_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(lean_object* v_cls_2007_, lean_object* v_msg_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v_cls_2007_, v_msg_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(lean_object* v___x_2015_, lean_object* v_as_2016_, size_t v_sz_2017_, size_t v_i_2018_, lean_object* v_b_2019_){
_start:
{
lean_object* v_a_2022_; uint8_t v___x_2026_; 
v___x_2026_ = lean_usize_dec_lt(v_i_2018_, v_sz_2017_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v_b_2019_);
return v___x_2027_;
}
else
{
lean_object* v_a_2028_; lean_object* v_defValue_2029_; uint8_t v___x_2030_; uint8_t v___y_2044_; uint8_t v___x_2045_; 
v_a_2028_ = lean_array_uget(v_as_2016_, v_i_2018_);
v_defValue_2029_ = lean_ctor_get(v_a_2028_, 1);
v___x_2030_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2015_, v_a_2028_);
v___x_2045_ = lean_unbox(v_defValue_2029_);
if (v___x_2045_ == 0)
{
if (v___x_2030_ == 0)
{
v___y_2044_ = v___x_2026_;
goto v___jp_2043_;
}
else
{
goto v___jp_2031_;
}
}
else
{
v___y_2044_ = v___x_2030_;
goto v___jp_2043_;
}
v___jp_2031_:
{
lean_object* v_name_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2041_; 
v_name_2032_ = lean_ctor_get(v_a_2028_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_a_2028_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_a_2028_, 1);
lean_dec(v_unused_2042_);
v___x_2034_ = v_a_2028_;
v_isShared_2035_ = v_isSharedCheck_2041_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_name_2032_);
lean_dec(v_a_2028_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2041_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2036_, 0, v___x_2030_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v___x_2036_);
v___x_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_name_2032_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; 
v___x_2039_ = lean_array_push(v_b_2019_, v___x_2038_);
v_a_2022_ = v___x_2039_;
goto v___jp_2021_;
}
}
}
v___jp_2043_:
{
if (v___y_2044_ == 0)
{
goto v___jp_2031_;
}
else
{
lean_dec(v_a_2028_);
v_a_2022_ = v_b_2019_;
goto v___jp_2021_;
}
}
}
v___jp_2021_:
{
size_t v___x_2023_; size_t v___x_2024_; 
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_2018_, v___x_2023_);
v_i_2018_ = v___x_2024_;
v_b_2019_ = v_a_2022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(lean_object* v___x_2046_, lean_object* v_as_2047_, lean_object* v_sz_2048_, lean_object* v_i_2049_, lean_object* v_b_2050_, lean_object* v___y_2051_){
_start:
{
size_t v_sz_boxed_2052_; size_t v_i_boxed_2053_; lean_object* v_res_2054_; 
v_sz_boxed_2052_ = lean_unbox_usize(v_sz_2048_);
lean_dec(v_sz_2048_);
v_i_boxed_2053_ = lean_unbox_usize(v_i_2049_);
lean_dec(v_i_2049_);
v_res_2054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2046_, v_as_2047_, v_sz_boxed_2052_, v_i_boxed_2053_, v_b_2050_);
lean_dec_ref(v_as_2047_);
lean_dec_ref(v___x_2046_);
return v_res_2054_;
}
}
static size_t _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1(void){
_start:
{
lean_object* v___x_2057_; size_t v_sz_2058_; 
v___x_2057_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2058_ = lean_array_size(v___x_2057_);
return v_sz_2058_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__1, &l_Lean_Meta_withEqnOptions___redArg___closed__1_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__1);
v___x_2060_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
lean_ctor_set(v___x_2060_, 2, v___x_2059_);
lean_ctor_set(v___x_2060_, 3, v___x_2059_);
lean_ctor_set(v___x_2060_, 4, v___x_2059_);
lean_ctor_set(v___x_2060_, 5, v___x_2059_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2069_ = l_Lean_Name_append(v___x_2068_, v___x_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__7));
v___x_2072_ = l_Lean_stringToMessageData(v___x_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions(lean_object* v_declName_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_toCold_2079_; lean_object* v_options_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; size_t v_sz_2084_; size_t v___x_2085_; lean_object* v___x_2086_; 
v_toCold_2079_ = lean_ctor_get(v_a_2076_, 0);
v_options_2080_ = lean_ctor_get(v_a_2076_, 1);
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__0));
v___x_2083_ = l_Lean_Meta_eqnAffectingOptions;
v_sz_2084_ = lean_usize_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__1, &l_Lean_Meta_saveEqnAffectingOptions___closed__1_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1);
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_2080_, v___x_2083_, v_sz_2084_, v___x_2085_, v___x_2082_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2147_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2147_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2147_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = lean_array_get_size(v_a_2087_);
v___x_2135_ = lean_nat_dec_eq(v___x_2134_, v___x_2081_);
if (v___x_2135_ == 0)
{
uint8_t v_hasTrace_2136_; 
v_hasTrace_2136_ = lean_ctor_get_uint8(v_options_2080_, sizeof(void*)*1);
if (v_hasTrace_2136_ == 0)
{
v___y_2092_ = v_a_2075_;
v___y_2093_ = v_a_2077_;
goto v___jp_2091_;
}
else
{
lean_object* v_inheritedTraceOptions_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_inheritedTraceOptions_2137_ = lean_ctor_get(v_toCold_2079_, 4);
v___x_2138_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_2139_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__6, &l_Lean_Meta_saveEqnAffectingOptions___closed__6_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6);
v___x_2140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2137_, v_options_2080_, v___x_2139_);
if (v___x_2140_ == 0)
{
v___y_2092_ = v_a_2075_;
v___y_2093_ = v_a_2077_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2141_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__8, &l_Lean_Meta_saveEqnAffectingOptions___closed__8_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8);
lean_inc(v_declName_2073_);
v___x_2142_ = l_Lean_MessageData_ofName(v_declName_2073_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(v___x_2138_, v___x_2143_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_dec_ref_known(v___x_2144_, 1);
v___y_2092_ = v_a_2075_;
v___y_2093_ = v_a_2077_;
goto v___jp_2091_;
}
else
{
lean_del_object(v___x_2089_);
lean_dec(v_a_2087_);
lean_dec(v_declName_2073_);
return v___x_2144_;
}
}
}
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_del_object(v___x_2089_);
lean_dec(v_a_2087_);
lean_dec(v_declName_2073_);
v___x_2145_ = lean_box(0);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
v___jp_2091_:
{
lean_object* v___x_2094_; lean_object* v_env_2095_; lean_object* v_nextMacroScope_2096_; lean_object* v_ngen_2097_; lean_object* v_auxDeclNGen_2098_; lean_object* v_traceState_2099_; lean_object* v_messages_2100_; lean_object* v_infoState_2101_; lean_object* v_snapshotTasks_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2132_; 
v___x_2094_ = lean_st_ref_take(v___y_2093_);
v_env_2095_ = lean_ctor_get(v___x_2094_, 0);
v_nextMacroScope_2096_ = lean_ctor_get(v___x_2094_, 1);
v_ngen_2097_ = lean_ctor_get(v___x_2094_, 2);
v_auxDeclNGen_2098_ = lean_ctor_get(v___x_2094_, 3);
v_traceState_2099_ = lean_ctor_get(v___x_2094_, 4);
v_messages_2100_ = lean_ctor_get(v___x_2094_, 6);
v_infoState_2101_ = lean_ctor_get(v___x_2094_, 7);
v_snapshotTasks_2102_ = lean_ctor_get(v___x_2094_, 8);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v___x_2094_, 5);
lean_dec(v_unused_2133_);
v___x_2104_ = v___x_2094_;
v_isShared_2105_ = v_isSharedCheck_2132_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snapshotTasks_2102_);
lean_inc(v_infoState_2101_);
lean_inc(v_messages_2100_);
lean_inc(v_traceState_2099_);
lean_inc(v_auxDeclNGen_2098_);
lean_inc(v_ngen_2097_);
lean_inc(v_nextMacroScope_2096_);
lean_inc(v_env_2095_);
lean_dec(v___x_2094_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2132_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2106_ = l_Lean_Meta_eqnOptionsExt;
v___x_2107_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2106_, v_env_2095_, v_declName_2073_, v_a_2087_);
v___x_2108_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 5, v___x_2108_);
lean_ctor_set(v___x_2104_, 0, v___x_2107_);
v___x_2110_ = v___x_2104_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_nextMacroScope_2096_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_ngen_2097_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_auxDeclNGen_2098_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v_traceState_2099_);
lean_ctor_set(v_reuseFailAlloc_2131_, 5, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2131_, 6, v_messages_2100_);
lean_ctor_set(v_reuseFailAlloc_2131_, 7, v_infoState_2101_);
lean_ctor_set(v_reuseFailAlloc_2131_, 8, v_snapshotTasks_2102_);
v___x_2110_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_mctx_2113_; lean_object* v_zetaDeltaFVarIds_2114_; lean_object* v_postponed_2115_; lean_object* v_diag_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2129_; 
v___x_2111_ = lean_st_ref_put(v___y_2093_, v___x_2110_);
v___x_2112_ = lean_st_ref_take(v___y_2092_);
v_mctx_2113_ = lean_ctor_get(v___x_2112_, 0);
v_zetaDeltaFVarIds_2114_ = lean_ctor_get(v___x_2112_, 2);
v_postponed_2115_ = lean_ctor_get(v___x_2112_, 3);
v_diag_2116_ = lean_ctor_get(v___x_2112_, 4);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2112_, 1);
lean_dec(v_unused_2130_);
v___x_2118_ = v___x_2112_;
v_isShared_2119_ = v_isSharedCheck_2129_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_diag_2116_);
lean_inc(v_postponed_2115_);
lean_inc(v_zetaDeltaFVarIds_2114_);
lean_inc(v_mctx_2113_);
lean_dec(v___x_2112_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2129_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 1, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_mctx_2113_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_zetaDeltaFVarIds_2114_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_postponed_2115_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_diag_2116_);
v___x_2122_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_st_ref_put(v___y_2092_, v___x_2122_);
v___x_2124_ = lean_box(0);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2124_);
v___x_2126_ = v___x_2089_;
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
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_declName_2073_);
v_a_2148_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2086_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2086_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_saveEqnAffectingOptions___boxed(lean_object* v_declName_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Meta_saveEqnAffectingOptions(v_declName_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(lean_object* v___x_2163_, lean_object* v_as_2164_, size_t v_sz_2165_, size_t v_i_2166_, lean_object* v_b_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_2163_, v_as_2164_, v_sz_2165_, v_i_2166_, v_b_2167_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(lean_object* v___x_2174_, lean_object* v_as_2175_, lean_object* v_sz_2176_, lean_object* v_i_2177_, lean_object* v_b_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
size_t v_sz_boxed_2184_; size_t v_i_boxed_2185_; lean_object* v_res_2186_; 
v_sz_boxed_2184_ = lean_unbox_usize(v_sz_2176_);
lean_dec(v_sz_2176_);
v_i_boxed_2185_ = lean_unbox_usize(v_i_2177_);
lean_dec(v_i_2177_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_2174_, v_as_2175_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec_ref(v_as_2175_);
lean_dec_ref(v___x_2174_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_box(0);
v___x_2189_ = lean_st_mk_ref(v___x_2188_);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* v_f_2193_){
_start:
{
uint8_t v___x_2195_; 
v___x_2195_ = l_Lean_initializing();
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref(v_f_2193_);
v___x_2196_ = lean_obj_once(&l_Lean_Meta_registerGetEqnsFn___closed__1, &l_Lean_Meta_registerGetEqnsFn___closed__1_once, _init_l_Lean_Meta_registerGetEqnsFn___closed__1);
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2198_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2199_ = lean_st_ref_take(v___x_2198_);
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_f_2193_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = lean_st_ref_put(v___x_2198_, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___boxed(lean_object* v_f_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_2203_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* v_declName_2209_, lean_object* v_as_x27_2210_, lean_object* v_b_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
if (lean_obj_tag(v_as_x27_2210_) == 0)
{
lean_object* v___x_2217_; 
lean_dec(v_declName_2209_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_b_2211_);
return v___x_2217_;
}
else
{
lean_object* v_head_2218_; lean_object* v_tail_2219_; lean_object* v___x_2220_; 
lean_dec_ref(v_b_2211_);
v_head_2218_ = lean_ctor_get(v_as_x27_2210_, 0);
v_tail_2219_ = lean_ctor_get(v_as_x27_2210_, 1);
lean_inc(v_head_2218_);
lean_inc(v___y_2215_);
lean_inc_ref(v___y_2214_);
lean_inc(v___y_2213_);
lean_inc_ref(v___y_2212_);
lean_inc(v_declName_2209_);
v___x_2220_ = lean_apply_6(v_head_2218_, v_declName_2209_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, lean_box(0));
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2233_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2233_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2233_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_box(0);
if (lean_obj_tag(v_a_2221_) == 1)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
lean_dec(v_declName_2209_);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_a_2221_);
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___x_2225_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2227_);
v___x_2229_ = v___x_2223_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
else
{
lean_object* v___x_2231_; 
lean_del_object(v___x_2223_);
lean_dec(v_a_2221_);
v___x_2231_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v_as_x27_2210_ = v_tail_2219_;
v_b_2211_ = v___x_2231_;
goto _start;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_declName_2209_);
v_a_2234_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2220_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2220_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(lean_object* v_declName_2242_, lean_object* v_as_x27_2243_, lean_object* v_b_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2242_, v_as_x27_2243_, v_b_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v_as_x27_2243_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* v___x_2251_, lean_object* v_declName_2252_, uint8_t v_nonRec_2253_, lean_object* v___x_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2263_; lean_object* v_env_2264_; uint8_t v___x_2265_; uint8_t v___x_2266_; 
v___x_2263_ = lean_st_ref_get(v___y_2258_);
v_env_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_ref(v_env_2264_);
lean_dec(v___x_2263_);
v___x_2265_ = 1;
lean_inc(v___x_2251_);
v___x_2266_ = l_Lean_Environment_contains(v_env_2264_, v___x_2251_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; 
lean_dec(v___x_2251_);
lean_inc(v_declName_2252_);
v___x_2267_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(v_declName_2252_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; uint8_t v___x_2269_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = lean_unbox(v_a_2268_);
lean_dec(v_a_2268_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v___x_2254_);
lean_dec(v_declName_2252_);
goto v___jp_2260_;
}
else
{
lean_object* v___x_2270_; 
lean_inc(v_declName_2252_);
v___x_2270_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_2252_, v___y_2258_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; uint8_t v___x_2272_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = lean_unbox(v_a_2271_);
lean_dec(v_a_2271_);
if (v___x_2272_ == 0)
{
if (v_nonRec_2253_ == 0)
{
lean_dec_ref(v___x_2254_);
lean_dec(v_declName_2252_);
goto v___jp_2260_;
}
else
{
lean_object* v___x_2273_; lean_object* v_env_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2273_ = lean_st_ref_get(v___y_2258_);
v_env_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc_ref(v_env_2274_);
lean_dec(v___x_2273_);
lean_inc(v_declName_2252_);
v___x_2275_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2274_, v_declName_2252_, v___x_2254_);
v___x_2276_ = l_Lean_Meta_mkSimpleEqThm(v_declName_2252_, v___x_2275_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2276_;
}
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec_ref(v___x_2254_);
v___x_2277_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
v___x_2278_ = lean_st_ref_get(v___x_2277_);
v___x_2279_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0));
v___x_2280_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2252_, v___x_2278_, v___x_2279_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___x_2278_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2290_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2290_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2290_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_fst_2285_; 
v_fst_2285_ = lean_ctor_get(v_a_2281_, 0);
lean_inc(v_fst_2285_);
lean_dec(v_a_2281_);
if (lean_obj_tag(v_fst_2285_) == 0)
{
lean_del_object(v___x_2283_);
goto v___jp_2260_;
}
else
{
lean_object* v_val_2286_; lean_object* v___x_2288_; 
v_val_2286_ = lean_ctor_get(v_fst_2285_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v_fst_2285_, 1);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v_val_2286_);
v___x_2288_ = v___x_2283_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_val_2286_);
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
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
v_a_2291_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2280_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2280_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v___x_2254_);
lean_dec(v_declName_2252_);
v_a_2299_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2270_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2270_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v___x_2254_);
lean_dec(v_declName_2252_);
v_a_2307_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2267_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2267_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_dec_ref(v___x_2254_);
lean_dec(v_declName_2252_);
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2251_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
v___jp_2260_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* v___x_2317_, lean_object* v_declName_2318_, lean_object* v_nonRec_2319_, lean_object* v___x_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v_nonRec_boxed_2326_; lean_object* v_res_2327_; 
v_nonRec_boxed_2326_ = lean_unbox(v_nonRec_2319_);
v_res_2327_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(v___x_2317_, v_declName_2318_, v_nonRec_boxed_2326_, v___x_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(lean_object* v_msg_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_ref_2334_; lean_object* v___x_2335_; lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2344_; 
v_ref_2334_ = lean_ctor_get(v___y_2331_, 4);
v___x_2335_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
lean_inc(v_ref_2334_);
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_ref_2334_);
lean_ctor_set(v___x_2340_, 1, v_a_2336_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 1);
lean_ctor_set(v___x_2338_, 0, v___x_2340_);
v___x_2342_ = v___x_2338_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(lean_object* v_msg_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2352_, uint8_t v_isExporting_2353_, lean_object* v___x_2354_, lean_object* v___y_2355_, lean_object* v___x_2356_, lean_object* v_a_x3f_2357_){
_start:
{
lean_object* v___x_2359_; lean_object* v_env_2360_; lean_object* v_nextMacroScope_2361_; lean_object* v_ngen_2362_; lean_object* v_auxDeclNGen_2363_; lean_object* v_traceState_2364_; lean_object* v_messages_2365_; lean_object* v_infoState_2366_; lean_object* v_snapshotTasks_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2392_; 
v___x_2359_ = lean_st_ref_take(v___y_2352_);
v_env_2360_ = lean_ctor_get(v___x_2359_, 0);
v_nextMacroScope_2361_ = lean_ctor_get(v___x_2359_, 1);
v_ngen_2362_ = lean_ctor_get(v___x_2359_, 2);
v_auxDeclNGen_2363_ = lean_ctor_get(v___x_2359_, 3);
v_traceState_2364_ = lean_ctor_get(v___x_2359_, 4);
v_messages_2365_ = lean_ctor_get(v___x_2359_, 6);
v_infoState_2366_ = lean_ctor_get(v___x_2359_, 7);
v_snapshotTasks_2367_ = lean_ctor_get(v___x_2359_, 8);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v___x_2359_, 5);
lean_dec(v_unused_2393_);
v___x_2369_ = v___x_2359_;
v_isShared_2370_ = v_isSharedCheck_2392_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_snapshotTasks_2367_);
lean_inc(v_infoState_2366_);
lean_inc(v_messages_2365_);
lean_inc(v_traceState_2364_);
lean_inc(v_auxDeclNGen_2363_);
lean_inc(v_ngen_2362_);
lean_inc(v_nextMacroScope_2361_);
lean_inc(v_env_2360_);
lean_dec(v___x_2359_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2392_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2371_ = l_Lean_Environment_setExporting(v_env_2360_, v_isExporting_2353_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 5, v___x_2354_);
lean_ctor_set(v___x_2369_, 0, v___x_2371_);
v___x_2373_ = v___x_2369_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_nextMacroScope_2361_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v_ngen_2362_);
lean_ctor_set(v_reuseFailAlloc_2391_, 3, v_auxDeclNGen_2363_);
lean_ctor_set(v_reuseFailAlloc_2391_, 4, v_traceState_2364_);
lean_ctor_set(v_reuseFailAlloc_2391_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2391_, 6, v_messages_2365_);
lean_ctor_set(v_reuseFailAlloc_2391_, 7, v_infoState_2366_);
lean_ctor_set(v_reuseFailAlloc_2391_, 8, v_snapshotTasks_2367_);
v___x_2373_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_mctx_2376_; lean_object* v_zetaDeltaFVarIds_2377_; lean_object* v_postponed_2378_; lean_object* v_diag_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2389_; 
v___x_2374_ = lean_st_ref_put(v___y_2352_, v___x_2373_);
v___x_2375_ = lean_st_ref_take(v___y_2355_);
v_mctx_2376_ = lean_ctor_get(v___x_2375_, 0);
v_zetaDeltaFVarIds_2377_ = lean_ctor_get(v___x_2375_, 2);
v_postponed_2378_ = lean_ctor_get(v___x_2375_, 3);
v_diag_2379_ = lean_ctor_get(v___x_2375_, 4);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2375_, 1);
lean_dec(v_unused_2390_);
v___x_2381_ = v___x_2375_;
v_isShared_2382_ = v_isSharedCheck_2389_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_diag_2379_);
lean_inc(v_postponed_2378_);
lean_inc(v_zetaDeltaFVarIds_2377_);
lean_inc(v_mctx_2376_);
lean_dec(v___x_2375_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2389_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 1, v___x_2356_);
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_mctx_2376_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_zetaDeltaFVarIds_2377_);
lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_postponed_2378_);
lean_ctor_set(v_reuseFailAlloc_2388_, 4, v_diag_2379_);
v___x_2384_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = lean_st_ref_put(v___y_2355_, v___x_2384_);
v___x_2386_ = lean_box(0);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2394_, lean_object* v_isExporting_2395_, lean_object* v___x_2396_, lean_object* v___y_2397_, lean_object* v___x_2398_, lean_object* v_a_x3f_2399_, lean_object* v___y_2400_){
_start:
{
uint8_t v_isExporting_boxed_2401_; lean_object* v_res_2402_; 
v_isExporting_boxed_2401_ = lean_unbox(v_isExporting_2395_);
v_res_2402_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2394_, v_isExporting_boxed_2401_, v___x_2396_, v___y_2397_, v___x_2398_, v_a_x3f_2399_);
lean_dec(v_a_x3f_2399_);
lean_dec(v___y_2397_);
lean_dec(v___y_2394_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_2403_, uint8_t v_isExporting_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v_env_2411_; lean_object* v___x_2412_; uint8_t v_isModule_2413_; 
v___x_2410_ = lean_st_ref_get(v___y_2408_);
v_env_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc_ref(v_env_2411_);
lean_dec(v___x_2410_);
v___x_2412_ = l_Lean_Environment_header(v_env_2411_);
v_isModule_2413_ = lean_ctor_get_uint8(v___x_2412_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2412_);
if (v_isModule_2413_ == 0)
{
lean_object* v___x_2414_; 
lean_dec_ref(v_env_2411_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
v___x_2414_ = lean_apply_5(v_x_2403_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, lean_box(0));
return v___x_2414_;
}
else
{
uint8_t v_isExporting_2415_; 
v_isExporting_2415_ = lean_ctor_get_uint8(v_env_2411_, sizeof(void*)*8);
lean_dec_ref(v_env_2411_);
if (v_isExporting_2404_ == 0)
{
if (v_isExporting_2415_ == 0)
{
lean_object* v___x_2481_; 
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
v___x_2481_ = lean_apply_5(v_x_2403_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, lean_box(0));
return v___x_2481_;
}
else
{
goto v___jp_2416_;
}
}
else
{
if (v_isExporting_2415_ == 0)
{
goto v___jp_2416_;
}
else
{
lean_object* v___x_2482_; 
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
v___x_2482_ = lean_apply_5(v_x_2403_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, lean_box(0));
return v___x_2482_;
}
}
v___jp_2416_:
{
lean_object* v___x_2417_; lean_object* v_env_2418_; lean_object* v_nextMacroScope_2419_; lean_object* v_ngen_2420_; lean_object* v_auxDeclNGen_2421_; lean_object* v_traceState_2422_; lean_object* v_messages_2423_; lean_object* v_infoState_2424_; lean_object* v_snapshotTasks_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2479_; 
v___x_2417_ = lean_st_ref_take(v___y_2408_);
v_env_2418_ = lean_ctor_get(v___x_2417_, 0);
v_nextMacroScope_2419_ = lean_ctor_get(v___x_2417_, 1);
v_ngen_2420_ = lean_ctor_get(v___x_2417_, 2);
v_auxDeclNGen_2421_ = lean_ctor_get(v___x_2417_, 3);
v_traceState_2422_ = lean_ctor_get(v___x_2417_, 4);
v_messages_2423_ = lean_ctor_get(v___x_2417_, 6);
v_infoState_2424_ = lean_ctor_get(v___x_2417_, 7);
v_snapshotTasks_2425_ = lean_ctor_get(v___x_2417_, 8);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2417_, 5);
lean_dec(v_unused_2480_);
v___x_2427_ = v___x_2417_;
v_isShared_2428_ = v_isSharedCheck_2479_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_snapshotTasks_2425_);
lean_inc(v_infoState_2424_);
lean_inc(v_messages_2423_);
lean_inc(v_traceState_2422_);
lean_inc(v_auxDeclNGen_2421_);
lean_inc(v_ngen_2420_);
lean_inc(v_nextMacroScope_2419_);
lean_inc(v_env_2418_);
lean_dec(v___x_2417_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2479_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2429_ = l_Lean_Environment_setExporting(v_env_2418_, v_isExporting_2404_);
v___x_2430_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 5, v___x_2430_);
lean_ctor_set(v___x_2427_, 0, v___x_2429_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_nextMacroScope_2419_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_ngen_2420_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_auxDeclNGen_2421_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v_traceState_2422_);
lean_ctor_set(v_reuseFailAlloc_2478_, 5, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2478_, 6, v_messages_2423_);
lean_ctor_set(v_reuseFailAlloc_2478_, 7, v_infoState_2424_);
lean_ctor_set(v_reuseFailAlloc_2478_, 8, v_snapshotTasks_2425_);
v___x_2432_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_mctx_2435_; lean_object* v_zetaDeltaFVarIds_2436_; lean_object* v_postponed_2437_; lean_object* v_diag_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2476_; 
v___x_2433_ = lean_st_ref_put(v___y_2408_, v___x_2432_);
v___x_2434_ = lean_st_ref_take(v___y_2406_);
v_mctx_2435_ = lean_ctor_get(v___x_2434_, 0);
v_zetaDeltaFVarIds_2436_ = lean_ctor_get(v___x_2434_, 2);
v_postponed_2437_ = lean_ctor_get(v___x_2434_, 3);
v_diag_2438_ = lean_ctor_get(v___x_2434_, 4);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2434_, 1);
lean_dec(v_unused_2477_);
v___x_2440_ = v___x_2434_;
v_isShared_2441_ = v_isSharedCheck_2476_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_diag_2438_);
lean_inc(v_postponed_2437_);
lean_inc(v_zetaDeltaFVarIds_2436_);
lean_inc(v_mctx_2435_);
lean_dec(v___x_2434_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2476_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2442_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 1, v___x_2442_);
v___x_2444_ = v___x_2440_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_mctx_2435_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_zetaDeltaFVarIds_2436_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_postponed_2437_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_diag_2438_);
v___x_2444_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v_r_2446_; 
v___x_2445_ = lean_st_ref_put(v___y_2406_, v___x_2444_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
v_r_2446_ = lean_apply_5(v_x_2403_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, lean_box(0));
if (lean_obj_tag(v_r_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2463_; 
v_a_2447_ = lean_ctor_get(v_r_2446_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_r_2446_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2449_ = v_r_2446_;
v_isShared_2450_ = v_isSharedCheck_2463_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v_r_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2463_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
lean_inc(v_a_2447_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set_tag(v___x_2449_, 1);
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
v___x_2453_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2408_, v_isExporting_2415_, v___x_2430_, v___y_2406_, v___x_2442_, v___x_2452_);
lean_dec_ref(v___x_2452_);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v___x_2453_, 0);
lean_dec(v_unused_2461_);
v___x_2455_ = v___x_2453_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_dec(v___x_2453_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v_a_2447_);
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2447_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_a_2464_ = lean_ctor_get(v_r_2446_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v_r_2446_, 1);
v___x_2465_ = lean_box(0);
v___x_2466_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2408_, v_isExporting_2415_, v___x_2430_, v___y_2406_, v___x_2442_, v___x_2465_);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v___x_2466_, 0);
lean_dec(v_unused_2474_);
v___x_2468_ = v___x_2466_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_dec(v___x_2466_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set_tag(v___x_2468_, 1);
lean_ctor_set(v___x_2468_, 0, v_a_2464_);
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2464_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2483_, lean_object* v_isExporting_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v_isExporting_boxed_2490_; lean_object* v_res_2491_; 
v_isExporting_boxed_2490_ = lean_unbox(v_isExporting_2484_);
v_res_2491_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2483_, v_isExporting_boxed_2490_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(lean_object* v_x_2492_, uint8_t v_when_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
if (v_when_2493_ == 0)
{
lean_object* v___x_2499_; 
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
v___x_2499_ = lean_apply_5(v_x_2492_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, lean_box(0));
return v___x_2499_;
}
else
{
uint8_t v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = 0;
v___x_2501_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2492_, v___x_2500_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(lean_object* v_x_2502_, lean_object* v_when_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v_when_boxed_2509_; lean_object* v_res_2510_; 
v_when_boxed_2509_ = lean_unbox(v_when_2503_);
v_res_2510_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2502_, v_when_boxed_2509_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2510_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0));
v___x_2513_ = l_Lean_stringToMessageData(v___x_2512_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2));
v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4));
v___x_2519_ = l_Lean_stringToMessageData(v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* v_declName_2520_, uint8_t v_nonRec_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; lean_object* v_env_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___f_2532_; uint8_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2527_ = lean_st_ref_get(v___y_2525_);
v_env_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc_ref(v_env_2528_);
lean_dec(v___x_2527_);
v___x_2529_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
lean_inc(v_declName_2520_);
v___x_2530_ = l_Lean_Meta_mkEqLikeNameFor(v_env_2528_, v_declName_2520_, v___x_2529_);
v___x_2531_ = lean_box(v_nonRec_2521_);
lean_inc(v___x_2530_);
v___f_2532_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2532_, 0, v___x_2530_);
lean_closure_set(v___f_2532_, 1, v_declName_2520_);
lean_closure_set(v___f_2532_, 2, v___x_2531_);
lean_closure_set(v___f_2532_, 3, v___x_2529_);
v___x_2533_ = 1;
v___x_2534_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v___f_2532_, v___x_2533_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
if (lean_obj_tag(v_a_2535_) == 1)
{
lean_object* v_val_2536_; uint8_t v___x_2537_; 
v_val_2536_ = lean_ctor_get(v_a_2535_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v_a_2535_, 1);
v___x_2537_ = lean_name_eq(v_val_2536_, v___x_2530_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec_ref_known(v___x_2534_, 1);
v___x_2538_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
v___x_2539_ = l_Lean_MessageData_ofName(v_val_2536_);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = l_Lean_MessageData_ofName(v___x_2530_);
v___x_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = lean_obj_once(&l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5, &l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once, _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
v___x_2546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_2546_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
lean_dec(v_val_2536_);
lean_dec(v___x_2530_);
return v___x_2534_;
}
}
else
{
lean_dec(v_a_2535_);
lean_dec(v___x_2530_);
return v___x_2534_;
}
}
else
{
lean_dec(v___x_2530_);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* v_declName_2556_, lean_object* v_nonRec_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
uint8_t v_nonRec_boxed_2563_; lean_object* v_res_2564_; 
v_nonRec_boxed_2563_ = lean_unbox(v_nonRec_2557_);
v_res_2564_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(v_declName_2556_, v_nonRec_boxed_2563_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* v_declName_2565_, uint8_t v_nonRec_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2572_ = lean_box(v_nonRec_2566_);
v___f_2573_ = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2573_, 0, v_declName_2565_);
lean_closure_set(v___f_2573_, 1, v___x_2572_);
v___x_2574_ = lean_unsigned_to_nat(32u);
v___x_2575_ = lean_mk_empty_array_with_capacity(v___x_2574_);
lean_dec_ref(v___x_2575_);
v___x_2576_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_2577_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3));
v___x_2578_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_2576_, v___x_2577_, v___f_2573_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* v_declName_2579_, lean_object* v_nonRec_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
uint8_t v_nonRec_boxed_2586_; lean_object* v_res_2587_; 
v_nonRec_boxed_2586_ = lean_unbox(v_nonRec_2580_);
v_res_2587_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_2579_, v_nonRec_boxed_2586_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* v_declName_2588_, lean_object* v_as_2589_, lean_object* v_as_x27_2590_, lean_object* v_b_2591_, lean_object* v_a_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_2588_, v_as_x27_2590_, v_b_2591_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* v_declName_2599_, lean_object* v_as_2600_, lean_object* v_as_x27_2601_, lean_object* v_b_2602_, lean_object* v_a_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(v_declName_2599_, v_as_2600_, v_as_x27_2601_, v_b_2602_, v_a_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v_as_x27_2601_);
lean_dec(v_as_2600_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(lean_object* v_00_u03b1_2610_, lean_object* v_x_2611_, uint8_t v_isExporting_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_2611_, v_isExporting_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2619_, lean_object* v_x_2620_, lean_object* v_isExporting_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
uint8_t v_isExporting_boxed_2627_; lean_object* v_res_2628_; 
v_isExporting_boxed_2627_ = lean_unbox(v_isExporting_2621_);
v_res_2628_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_2619_, v_x_2620_, v_isExporting_boxed_2627_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(lean_object* v_00_u03b1_2629_, lean_object* v_x_2630_, uint8_t v_when_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(v_x_2630_, v_when_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(lean_object* v_00_u03b1_2638_, lean_object* v_x_2639_, lean_object* v_when_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
uint8_t v_when_boxed_2646_; lean_object* v_res_2647_; 
v_when_boxed_2646_ = lean_unbox(v_when_2640_);
v_res_2647_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(v_00_u03b1_2638_, v_x_2639_, v_when_boxed_2646_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(lean_object* v_00_u03b1_2648_, lean_object* v_msg_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v_msg_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(lean_object* v_00_u03b1_2656_, lean_object* v_msg_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(v_00_u03b1_2656_, v_msg_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2663_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_unsigned_to_nat(32u);
v___x_2665_ = lean_mk_empty_array_with_capacity(v___x_2664_);
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
return v___x_2666_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2667_ = ((size_t)5ULL);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_unsigned_to_nat(32u);
v___x_2670_ = lean_mk_empty_array_with_capacity(v___x_2669_);
v___x_2671_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_2672_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v___x_2670_);
lean_ctor_set(v___x_2672_, 2, v___x_2668_);
lean_ctor_set(v___x_2672_, 3, v___x_2668_);
lean_ctor_set_usize(v___x_2672_, 4, v___x_2667_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; lean_object* v_traceState_2676_; lean_object* v_traces_2677_; lean_object* v___x_2678_; lean_object* v_traceState_2679_; lean_object* v_env_2680_; lean_object* v_nextMacroScope_2681_; lean_object* v_ngen_2682_; lean_object* v_auxDeclNGen_2683_; lean_object* v_cache_2684_; lean_object* v_messages_2685_; lean_object* v_infoState_2686_; lean_object* v_snapshotTasks_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2706_; 
v___x_2675_ = lean_st_ref_get(v___y_2673_);
v_traceState_2676_ = lean_ctor_get(v___x_2675_, 4);
lean_inc_ref(v_traceState_2676_);
lean_dec(v___x_2675_);
v_traces_2677_ = lean_ctor_get(v_traceState_2676_, 0);
lean_inc_ref(v_traces_2677_);
lean_dec_ref(v_traceState_2676_);
v___x_2678_ = lean_st_ref_take(v___y_2673_);
v_traceState_2679_ = lean_ctor_get(v___x_2678_, 4);
v_env_2680_ = lean_ctor_get(v___x_2678_, 0);
v_nextMacroScope_2681_ = lean_ctor_get(v___x_2678_, 1);
v_ngen_2682_ = lean_ctor_get(v___x_2678_, 2);
v_auxDeclNGen_2683_ = lean_ctor_get(v___x_2678_, 3);
v_cache_2684_ = lean_ctor_get(v___x_2678_, 5);
v_messages_2685_ = lean_ctor_get(v___x_2678_, 6);
v_infoState_2686_ = lean_ctor_get(v___x_2678_, 7);
v_snapshotTasks_2687_ = lean_ctor_get(v___x_2678_, 8);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2689_ = v___x_2678_;
v_isShared_2690_ = v_isSharedCheck_2706_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_snapshotTasks_2687_);
lean_inc(v_infoState_2686_);
lean_inc(v_messages_2685_);
lean_inc(v_cache_2684_);
lean_inc(v_traceState_2679_);
lean_inc(v_auxDeclNGen_2683_);
lean_inc(v_ngen_2682_);
lean_inc(v_nextMacroScope_2681_);
lean_inc(v_env_2680_);
lean_dec(v___x_2678_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2706_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
uint64_t v_tid_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2704_; 
v_tid_2691_ = lean_ctor_get_uint64(v_traceState_2679_, sizeof(void*)*1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_traceState_2679_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v_traceState_2679_, 0);
lean_dec(v_unused_2705_);
v___x_2693_ = v_traceState_2679_;
v_isShared_2694_ = v_isSharedCheck_2704_;
goto v_resetjp_2692_;
}
else
{
lean_dec(v_traceState_2679_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2704_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2695_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2695_);
v___x_2697_ = v___x_2693_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2695_);
lean_ctor_set_uint64(v_reuseFailAlloc_2703_, sizeof(void*)*1, v_tid_2691_);
v___x_2697_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2699_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 4, v___x_2697_);
v___x_2699_ = v___x_2689_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_env_2680_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_nextMacroScope_2681_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_ngen_2682_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_auxDeclNGen_2683_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2702_, 5, v_cache_2684_);
lean_ctor_set(v_reuseFailAlloc_2702_, 6, v_messages_2685_);
lean_ctor_set(v_reuseFailAlloc_2702_, 7, v_infoState_2686_);
lean_ctor_set(v_reuseFailAlloc_2702_, 8, v_snapshotTasks_2687_);
v___x_2699_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_st_ref_put(v___y_2673_, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_traces_2677_);
return v___x_2701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2707_);
lean_dec(v___y_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_____r_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = 0;
v___x_2723_ = lean_box(v___x_2722_);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_____r_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
return v_res_2729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2732_ = l_Lean_stringToMessageData(v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v_name_2733_, lean_object* v_x_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2738_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_2739_ = l_Lean_MessageData_ofName(v_name_2733_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_name_2742_, lean_object* v_x_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_2742_, v_x_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v_x_2743_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_2748_){
_start:
{
if (lean_obj_tag(v_x_2748_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
v_a_2750_ = lean_ctor_get(v_x_2748_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_x_2748_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v_x_2748_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v_x_2748_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set_tag(v___x_2752_, 1);
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
v_a_2758_ = lean_ctor_get(v_x_2748_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_x_2748_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v_x_2748_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v_x_2748_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set_tag(v___x_2760_, 0);
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_e_2769_){
_start:
{
if (lean_obj_tag(v_e_2769_) == 0)
{
uint8_t v___x_2770_; 
v___x_2770_ = 2;
return v___x_2770_;
}
else
{
lean_object* v_a_2771_; uint8_t v___x_2772_; 
v_a_2771_ = lean_ctor_get(v_e_2769_, 0);
v___x_2772_ = lean_unbox(v_a_2771_);
if (v___x_2772_ == 0)
{
uint8_t v___x_2773_; 
v___x_2773_ = 1;
return v___x_2773_;
}
else
{
uint8_t v___x_2774_; 
v___x_2774_ = 0;
return v___x_2774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_e_2775_){
_start:
{
uint8_t v_res_2776_; lean_object* v_r_2777_; 
v_res_2776_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_e_2775_);
lean_dec_ref(v_e_2775_);
v_r_2777_ = lean_box(v_res_2776_);
return v_r_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(size_t v_sz_2778_, size_t v_i_2779_, lean_object* v_bs_2780_){
_start:
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_usize_dec_lt(v_i_2779_, v_sz_2778_);
if (v___x_2781_ == 0)
{
return v_bs_2780_;
}
else
{
lean_object* v_v_2782_; lean_object* v_msg_2783_; lean_object* v___x_2784_; lean_object* v_bs_x27_2785_; size_t v___x_2786_; size_t v___x_2787_; lean_object* v___x_2788_; 
v_v_2782_ = lean_array_uget_borrowed(v_bs_2780_, v_i_2779_);
v_msg_2783_ = lean_ctor_get(v_v_2782_, 1);
lean_inc_ref(v_msg_2783_);
v___x_2784_ = lean_unsigned_to_nat(0u);
v_bs_x27_2785_ = lean_array_uset(v_bs_2780_, v_i_2779_, v___x_2784_);
v___x_2786_ = ((size_t)1ULL);
v___x_2787_ = lean_usize_add(v_i_2779_, v___x_2786_);
v___x_2788_ = lean_array_uset(v_bs_x27_2785_, v_i_2779_, v_msg_2783_);
v_i_2779_ = v___x_2787_;
v_bs_2780_ = v___x_2788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2790_, lean_object* v_i_2791_, lean_object* v_bs_2792_){
_start:
{
size_t v_sz_boxed_2793_; size_t v_i_boxed_2794_; lean_object* v_res_2795_; 
v_sz_boxed_2793_ = lean_unbox_usize(v_sz_2790_);
lean_dec(v_sz_2790_);
v_i_boxed_2794_ = lean_unbox_usize(v_i_2791_);
lean_dec(v_i_2791_);
v_res_2795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_boxed_2793_, v_i_boxed_2794_, v_bs_2792_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_oldTraces_2796_, lean_object* v_data_2797_, lean_object* v_ref_2798_, lean_object* v_msg_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_toCold_2803_; lean_object* v_options_2804_; lean_object* v_currRecDepth_2805_; lean_object* v_maxRecDepth_2806_; lean_object* v_ref_2807_; lean_object* v_currNamespace_2808_; lean_object* v_openDecls_2809_; lean_object* v_initHeartbeats_2810_; lean_object* v_maxHeartbeats_2811_; lean_object* v_currMacroScope_2812_; uint8_t v_diag_2813_; uint8_t v_suppressElabErrors_2814_; lean_object* v___x_2815_; lean_object* v_traceState_2816_; lean_object* v_traces_2817_; lean_object* v_ref_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; size_t v_sz_2821_; size_t v___x_2822_; lean_object* v___x_2823_; lean_object* v_msg_2824_; lean_object* v___x_2825_; lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2863_; 
v_toCold_2803_ = lean_ctor_get(v___y_2800_, 0);
v_options_2804_ = lean_ctor_get(v___y_2800_, 1);
v_currRecDepth_2805_ = lean_ctor_get(v___y_2800_, 2);
v_maxRecDepth_2806_ = lean_ctor_get(v___y_2800_, 3);
v_ref_2807_ = lean_ctor_get(v___y_2800_, 4);
v_currNamespace_2808_ = lean_ctor_get(v___y_2800_, 5);
v_openDecls_2809_ = lean_ctor_get(v___y_2800_, 6);
v_initHeartbeats_2810_ = lean_ctor_get(v___y_2800_, 7);
v_maxHeartbeats_2811_ = lean_ctor_get(v___y_2800_, 8);
v_currMacroScope_2812_ = lean_ctor_get(v___y_2800_, 9);
v_diag_2813_ = lean_ctor_get_uint8(v___y_2800_, sizeof(void*)*10);
v_suppressElabErrors_2814_ = lean_ctor_get_uint8(v___y_2800_, sizeof(void*)*10 + 1);
v___x_2815_ = lean_st_ref_get(v___y_2801_);
v_traceState_2816_ = lean_ctor_get(v___x_2815_, 4);
lean_inc_ref(v_traceState_2816_);
lean_dec(v___x_2815_);
v_traces_2817_ = lean_ctor_get(v_traceState_2816_, 0);
lean_inc_ref(v_traces_2817_);
lean_dec_ref(v_traceState_2816_);
v_ref_2818_ = l_Lean_replaceRef(v_ref_2798_, v_ref_2807_);
lean_inc(v_currMacroScope_2812_);
lean_inc(v_maxHeartbeats_2811_);
lean_inc(v_initHeartbeats_2810_);
lean_inc(v_openDecls_2809_);
lean_inc(v_currNamespace_2808_);
lean_inc(v_maxRecDepth_2806_);
lean_inc(v_currRecDepth_2805_);
lean_inc_ref(v_options_2804_);
lean_inc_ref(v_toCold_2803_);
v___x_2819_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2819_, 0, v_toCold_2803_);
lean_ctor_set(v___x_2819_, 1, v_options_2804_);
lean_ctor_set(v___x_2819_, 2, v_currRecDepth_2805_);
lean_ctor_set(v___x_2819_, 3, v_maxRecDepth_2806_);
lean_ctor_set(v___x_2819_, 4, v_ref_2818_);
lean_ctor_set(v___x_2819_, 5, v_currNamespace_2808_);
lean_ctor_set(v___x_2819_, 6, v_openDecls_2809_);
lean_ctor_set(v___x_2819_, 7, v_initHeartbeats_2810_);
lean_ctor_set(v___x_2819_, 8, v_maxHeartbeats_2811_);
lean_ctor_set(v___x_2819_, 9, v_currMacroScope_2812_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*10, v_diag_2813_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*10 + 1, v_suppressElabErrors_2814_);
v___x_2820_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2817_);
lean_dec_ref(v_traces_2817_);
v_sz_2821_ = lean_array_size(v___x_2820_);
v___x_2822_ = ((size_t)0ULL);
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_sz_2821_, v___x_2822_, v___x_2820_);
v_msg_2824_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2824_, 0, v_data_2797_);
lean_ctor_set(v_msg_2824_, 1, v_msg_2799_);
lean_ctor_set(v_msg_2824_, 2, v___x_2823_);
v___x_2825_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_2824_, v___x_2819_, v___y_2801_);
lean_dec_ref_known(v___x_2819_, 10);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2863_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2863_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v_traceState_2831_; lean_object* v_env_2832_; lean_object* v_nextMacroScope_2833_; lean_object* v_ngen_2834_; lean_object* v_auxDeclNGen_2835_; lean_object* v_cache_2836_; lean_object* v_messages_2837_; lean_object* v_infoState_2838_; lean_object* v_snapshotTasks_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2862_; 
v___x_2830_ = lean_st_ref_take(v___y_2801_);
v_traceState_2831_ = lean_ctor_get(v___x_2830_, 4);
v_env_2832_ = lean_ctor_get(v___x_2830_, 0);
v_nextMacroScope_2833_ = lean_ctor_get(v___x_2830_, 1);
v_ngen_2834_ = lean_ctor_get(v___x_2830_, 2);
v_auxDeclNGen_2835_ = lean_ctor_get(v___x_2830_, 3);
v_cache_2836_ = lean_ctor_get(v___x_2830_, 5);
v_messages_2837_ = lean_ctor_get(v___x_2830_, 6);
v_infoState_2838_ = lean_ctor_get(v___x_2830_, 7);
v_snapshotTasks_2839_ = lean_ctor_get(v___x_2830_, 8);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2841_ = v___x_2830_;
v_isShared_2842_ = v_isSharedCheck_2862_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_snapshotTasks_2839_);
lean_inc(v_infoState_2838_);
lean_inc(v_messages_2837_);
lean_inc(v_cache_2836_);
lean_inc(v_traceState_2831_);
lean_inc(v_auxDeclNGen_2835_);
lean_inc(v_ngen_2834_);
lean_inc(v_nextMacroScope_2833_);
lean_inc(v_env_2832_);
lean_dec(v___x_2830_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2862_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
uint64_t v_tid_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2860_; 
v_tid_2843_ = lean_ctor_get_uint64(v_traceState_2831_, sizeof(void*)*1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_traceState_2831_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; 
v_unused_2861_ = lean_ctor_get(v_traceState_2831_, 0);
lean_dec(v_unused_2861_);
v___x_2845_ = v_traceState_2831_;
v_isShared_2846_ = v_isSharedCheck_2860_;
goto v_resetjp_2844_;
}
else
{
lean_dec(v_traceState_2831_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2860_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v_ref_2798_);
lean_ctor_set(v___x_2847_, 1, v_a_2826_);
v___x_2848_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2796_, v___x_2847_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2848_);
v___x_2850_ = v___x_2845_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2848_);
lean_ctor_set_uint64(v_reuseFailAlloc_2859_, sizeof(void*)*1, v_tid_2843_);
v___x_2850_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2852_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 4, v___x_2850_);
v___x_2852_ = v___x_2841_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_env_2832_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_nextMacroScope_2833_);
lean_ctor_set(v_reuseFailAlloc_2858_, 2, v_ngen_2834_);
lean_ctor_set(v_reuseFailAlloc_2858_, 3, v_auxDeclNGen_2835_);
lean_ctor_set(v_reuseFailAlloc_2858_, 4, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2858_, 5, v_cache_2836_);
lean_ctor_set(v_reuseFailAlloc_2858_, 6, v_messages_2837_);
lean_ctor_set(v_reuseFailAlloc_2858_, 7, v_infoState_2838_);
lean_ctor_set(v_reuseFailAlloc_2858_, 8, v_snapshotTasks_2839_);
v___x_2852_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2853_ = lean_st_ref_put(v___y_2801_, v___x_2852_);
v___x_2854_ = lean_box(0);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2854_);
v___x_2856_ = v___x_2828_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_oldTraces_2864_, lean_object* v_data_2865_, lean_object* v_ref_2866_, lean_object* v_msg_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2864_, v_data_2865_, v_ref_2866_, v_msg_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2871_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0));
v___x_2874_ = l_Lean_stringToMessageData(v___x_2873_);
return v___x_2874_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_2875_; double v___x_2876_; 
v___x_2875_ = lean_unsigned_to_nat(1000u);
v___x_2876_ = lean_float_of_nat(v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(lean_object* v_cls_2877_, uint8_t v_collapsed_2878_, lean_object* v_tag_2879_, lean_object* v_opts_2880_, uint8_t v_clsEnabled_2881_, lean_object* v_oldTraces_2882_, lean_object* v_msg_2883_, lean_object* v_resStartStop_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_fst_2888_; lean_object* v_snd_2889_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v_data_2893_; lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; lean_object* v___y_2909_; lean_object* v_a_2910_; uint8_t v___y_2925_; double v___y_2956_; 
v_fst_2888_ = lean_ctor_get(v_resStartStop_2884_, 0);
lean_inc(v_fst_2888_);
v_snd_2889_ = lean_ctor_get(v_resStartStop_2884_, 1);
lean_inc(v_snd_2889_);
lean_dec_ref(v_resStartStop_2884_);
v_fst_2904_ = lean_ctor_get(v_snd_2889_, 0);
lean_inc(v_fst_2904_);
v_snd_2905_ = lean_ctor_get(v_snd_2889_, 1);
lean_inc(v_snd_2905_);
lean_dec(v_snd_2889_);
v___x_2906_ = l_Lean_trace_profiler;
v___x_2907_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2880_, v___x_2906_);
if (v___x_2907_ == 0)
{
v___y_2925_ = v___x_2907_;
goto v___jp_2924_;
}
else
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2962_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_2880_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; double v___x_2965_; double v___x_2966_; double v___x_2967_; 
v___x_2963_ = l_Lean_trace_profiler_threshold;
v___x_2964_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2880_, v___x_2963_);
v___x_2965_ = lean_float_of_nat(v___x_2964_);
v___x_2966_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2);
v___x_2967_ = lean_float_div(v___x_2965_, v___x_2966_);
v___y_2956_ = v___x_2967_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; double v___x_2970_; 
v___x_2968_ = l_Lean_trace_profiler_threshold;
v___x_2969_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_2880_, v___x_2968_);
v___x_2970_ = lean_float_of_nat(v___x_2969_);
v___y_2956_ = v___x_2970_;
goto v___jp_2955_;
}
}
v___jp_2890_:
{
lean_object* v___x_2894_; 
lean_inc(v___y_2892_);
v___x_2894_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_oldTraces_2882_, v_data_2893_, v___y_2892_, v___y_2891_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2895_; 
lean_dec_ref_known(v___x_2894_, 1);
v___x_2895_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2888_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_fst_2888_);
v_a_2896_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2894_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2894_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
v___jp_2908_:
{
uint8_t v_result_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; double v___x_2914_; lean_object* v_data_2915_; 
v_result_2911_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_fst_2888_);
v___x_2912_ = lean_box(v_result_2911_);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
v___x_2914_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
lean_inc_ref(v_tag_2879_);
lean_inc_ref(v___x_2913_);
lean_inc(v_cls_2877_);
v_data_2915_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2915_, 0, v_cls_2877_);
lean_ctor_set(v_data_2915_, 1, v___x_2913_);
lean_ctor_set(v_data_2915_, 2, v_tag_2879_);
lean_ctor_set_float(v_data_2915_, sizeof(void*)*3, v___x_2914_);
lean_ctor_set_float(v_data_2915_, sizeof(void*)*3 + 8, v___x_2914_);
lean_ctor_set_uint8(v_data_2915_, sizeof(void*)*3 + 16, v_collapsed_2878_);
if (v___x_2907_ == 0)
{
lean_dec_ref_known(v___x_2913_, 1);
lean_dec(v_snd_2905_);
lean_dec(v_fst_2904_);
lean_dec_ref(v_tag_2879_);
lean_dec(v_cls_2877_);
v___y_2891_ = v_a_2910_;
v___y_2892_ = v___y_2909_;
v_data_2893_ = v_data_2915_;
goto v___jp_2890_;
}
else
{
lean_object* v_data_2916_; double v___x_2917_; double v___x_2918_; 
lean_dec_ref_known(v_data_2915_, 3);
v_data_2916_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2916_, 0, v_cls_2877_);
lean_ctor_set(v_data_2916_, 1, v___x_2913_);
lean_ctor_set(v_data_2916_, 2, v_tag_2879_);
v___x_2917_ = lean_unbox_float(v_fst_2904_);
lean_dec(v_fst_2904_);
lean_ctor_set_float(v_data_2916_, sizeof(void*)*3, v___x_2917_);
v___x_2918_ = lean_unbox_float(v_snd_2905_);
lean_dec(v_snd_2905_);
lean_ctor_set_float(v_data_2916_, sizeof(void*)*3 + 8, v___x_2918_);
lean_ctor_set_uint8(v_data_2916_, sizeof(void*)*3 + 16, v_collapsed_2878_);
v___y_2891_ = v_a_2910_;
v___y_2892_ = v___y_2909_;
v_data_2893_ = v_data_2916_;
goto v___jp_2890_;
}
}
v___jp_2919_:
{
lean_object* v_ref_2920_; lean_object* v___x_2921_; 
v_ref_2920_ = lean_ctor_get(v___y_2885_, 4);
lean_inc(v___y_2886_);
lean_inc_ref(v___y_2885_);
lean_inc(v_fst_2888_);
v___x_2921_ = lean_apply_4(v_msg_2883_, v_fst_2888_, v___y_2885_, v___y_2886_, lean_box(0));
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v___y_2909_ = v_ref_2920_;
v_a_2910_ = v_a_2922_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2923_; 
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
v___y_2909_ = v_ref_2920_;
v_a_2910_ = v___x_2923_;
goto v___jp_2908_;
}
}
v___jp_2924_:
{
if (v_clsEnabled_2881_ == 0)
{
if (v___y_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v_traceState_2927_; lean_object* v_env_2928_; lean_object* v_nextMacroScope_2929_; lean_object* v_ngen_2930_; lean_object* v_auxDeclNGen_2931_; lean_object* v_cache_2932_; lean_object* v_messages_2933_; lean_object* v_infoState_2934_; lean_object* v_snapshotTasks_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_snd_2905_);
lean_dec(v_fst_2904_);
lean_dec_ref(v_msg_2883_);
lean_dec_ref(v_tag_2879_);
lean_dec(v_cls_2877_);
v___x_2926_ = lean_st_ref_take(v___y_2886_);
v_traceState_2927_ = lean_ctor_get(v___x_2926_, 4);
v_env_2928_ = lean_ctor_get(v___x_2926_, 0);
v_nextMacroScope_2929_ = lean_ctor_get(v___x_2926_, 1);
v_ngen_2930_ = lean_ctor_get(v___x_2926_, 2);
v_auxDeclNGen_2931_ = lean_ctor_get(v___x_2926_, 3);
v_cache_2932_ = lean_ctor_get(v___x_2926_, 5);
v_messages_2933_ = lean_ctor_get(v___x_2926_, 6);
v_infoState_2934_ = lean_ctor_get(v___x_2926_, 7);
v_snapshotTasks_2935_ = lean_ctor_get(v___x_2926_, 8);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2937_ = v___x_2926_;
v_isShared_2938_ = v_isSharedCheck_2954_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_snapshotTasks_2935_);
lean_inc(v_infoState_2934_);
lean_inc(v_messages_2933_);
lean_inc(v_cache_2932_);
lean_inc(v_traceState_2927_);
lean_inc(v_auxDeclNGen_2931_);
lean_inc(v_ngen_2930_);
lean_inc(v_nextMacroScope_2929_);
lean_inc(v_env_2928_);
lean_dec(v___x_2926_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2954_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
uint64_t v_tid_2939_; lean_object* v_traces_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2953_; 
v_tid_2939_ = lean_ctor_get_uint64(v_traceState_2927_, sizeof(void*)*1);
v_traces_2940_ = lean_ctor_get(v_traceState_2927_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_traceState_2927_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2942_ = v_traceState_2927_;
v_isShared_2943_ = v_isSharedCheck_2953_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_traces_2940_);
lean_dec(v_traceState_2927_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2953_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2882_, v_traces_2940_);
lean_dec_ref(v_traces_2940_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2944_);
v___x_2946_ = v___x_2942_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2944_);
lean_ctor_set_uint64(v_reuseFailAlloc_2952_, sizeof(void*)*1, v_tid_2939_);
v___x_2946_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2948_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 4, v___x_2946_);
v___x_2948_ = v___x_2937_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_env_2928_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_nextMacroScope_2929_);
lean_ctor_set(v_reuseFailAlloc_2951_, 2, v_ngen_2930_);
lean_ctor_set(v_reuseFailAlloc_2951_, 3, v_auxDeclNGen_2931_);
lean_ctor_set(v_reuseFailAlloc_2951_, 4, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2951_, 5, v_cache_2932_);
lean_ctor_set(v_reuseFailAlloc_2951_, 6, v_messages_2933_);
lean_ctor_set(v_reuseFailAlloc_2951_, 7, v_infoState_2934_);
lean_ctor_set(v_reuseFailAlloc_2951_, 8, v_snapshotTasks_2935_);
v___x_2948_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = lean_st_ref_put(v___y_2886_, v___x_2948_);
v___x_2950_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_2888_);
return v___x_2950_;
}
}
}
}
}
else
{
goto v___jp_2919_;
}
}
else
{
goto v___jp_2919_;
}
}
v___jp_2955_:
{
double v___x_2957_; double v___x_2958_; double v___x_2959_; uint8_t v___x_2960_; 
v___x_2957_ = lean_unbox_float(v_snd_2905_);
v___x_2958_ = lean_unbox_float(v_fst_2904_);
v___x_2959_ = lean_float_sub(v___x_2957_, v___x_2958_);
v___x_2960_ = lean_float_decLt(v___y_2956_, v___x_2959_);
v___y_2925_ = v___x_2960_;
goto v___jp_2924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(lean_object* v_cls_2971_, lean_object* v_collapsed_2972_, lean_object* v_tag_2973_, lean_object* v_opts_2974_, lean_object* v_clsEnabled_2975_, lean_object* v_oldTraces_2976_, lean_object* v_msg_2977_, lean_object* v_resStartStop_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
uint8_t v_collapsed_boxed_2982_; uint8_t v_clsEnabled_boxed_2983_; lean_object* v_res_2984_; 
v_collapsed_boxed_2982_ = lean_unbox(v_collapsed_2972_);
v_clsEnabled_boxed_2983_ = lean_unbox(v_clsEnabled_2975_);
v_res_2984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_2971_, v_collapsed_boxed_2982_, v_tag_2973_, v_opts_2974_, v_clsEnabled_boxed_2983_, v_oldTraces_2976_, v_msg_2977_, v_resStartStop_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v_opts_2974_);
return v_res_2984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2988_ = lean_unsigned_to_nat(0u);
v___x_2989_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
lean_ctor_set(v___x_2989_, 2, v___x_2988_);
lean_ctor_set(v___x_2989_, 3, v___x_2988_);
lean_ctor_set(v___x_2989_, 4, v___x_2987_);
lean_ctor_set(v___x_2989_, 5, v___x_2987_);
lean_ctor_set(v___x_2989_, 6, v___x_2987_);
lean_ctor_set(v___x_2989_, 7, v___x_2987_);
lean_ctor_set(v___x_2989_, 8, v___x_2987_);
lean_ctor_set(v___x_2989_, 9, v___x_2987_);
lean_ctor_set(v___x_2989_, 10, v___x_2987_);
return v___x_2989_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2991_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
lean_ctor_set(v___x_2991_, 2, v___x_2990_);
lean_ctor_set(v___x_2991_, 3, v___x_2990_);
lean_ctor_set(v___x_2991_, 4, v___x_2990_);
lean_ctor_set(v___x_2991_, 5, v___x_2990_);
return v___x_2991_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
v___x_2993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
lean_ctor_set(v___x_2993_, 2, v___x_2992_);
lean_ctor_set(v___x_2993_, 3, v___x_2992_);
lean_ctor_set(v___x_2993_, 4, v___x_2992_);
return v___x_2993_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_2998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_2999_ = l_Lean_Name_append(v___x_2998_, v___x_2997_);
return v___x_2999_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3000_; double v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(1000000000u);
v___x_3001_ = lean_float_of_nat(v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3002_, lean_object* v___f_3003_, lean_object* v_name_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_options_3008_; uint8_t v_hasTrace_3009_; 
v_options_3008_ = lean_ctor_get(v___y_3005_, 1);
v_hasTrace_3009_ = lean_ctor_get_uint8(v_options_3008_, sizeof(void*)*1);
if (v_hasTrace_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v_env_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___f_3003_);
v___x_3010_ = lean_st_ref_get(v___y_3006_);
v_env_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc_ref(v_env_3011_);
lean_dec(v___x_3010_);
lean_inc(v_name_3004_);
v___x_3012_ = l_Lean_Meta_declFromEqLikeName(v_env_3011_, v_name_3004_);
if (lean_obj_tag(v___x_3012_) == 1)
{
lean_object* v_val_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3118_; 
v_val_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3118_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_val_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3118_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_fst_3017_; lean_object* v_snd_3018_; lean_object* v___x_3019_; lean_object* v_env_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v_fst_3017_ = lean_ctor_get(v_val_3013_, 0);
lean_inc_n(v_fst_3017_, 2);
v_snd_3018_ = lean_ctor_get(v_val_3013_, 1);
lean_inc_n(v_snd_3018_, 2);
lean_dec(v_val_3013_);
v___x_3019_ = lean_st_ref_get(v___y_3006_);
v_env_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc_ref(v_env_3020_);
lean_dec(v___x_3019_);
v___x_3021_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3020_, v_fst_3017_, v_snd_3018_);
v___x_3022_ = lean_name_eq(v_name_3004_, v___x_3021_);
lean_dec(v___x_3021_);
lean_dec(v_name_3004_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_dec(v_snd_3018_);
lean_dec(v_fst_3017_);
lean_dec(v___x_3002_);
v___x_3023_ = lean_box(v_hasTrace_3009_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set_tag(v___x_3015_, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3023_);
v___x_3025_ = v___x_3015_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
else
{
uint8_t v___x_3027_; lean_object* v_a_3029_; 
lean_inc(v_snd_3018_);
v___x_3027_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3018_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3043_; uint8_t v___x_3044_; lean_object* v_a_3046_; 
lean_del_object(v___x_3015_);
v___x_3043_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3044_ = lean_string_dec_eq(v_snd_3018_, v___x_3043_);
lean_dec(v_snd_3018_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
lean_dec(v_fst_3017_);
lean_dec(v___x_3002_);
v___x_3058_ = lean_box(v_hasTrace_3009_);
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
return v___x_3059_;
}
else
{
uint8_t v___x_3060_; uint8_t v___x_3061_; uint8_t v___x_3062_; lean_object* v___x_3063_; uint64_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3060_ = 1;
v___x_3061_ = 0;
v___x_3062_ = 2;
v___x_3063_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3063_, 0, v___x_3027_);
lean_ctor_set_uint8(v___x_3063_, 1, v___x_3027_);
lean_ctor_set_uint8(v___x_3063_, 2, v___x_3027_);
lean_ctor_set_uint8(v___x_3063_, 3, v___x_3027_);
lean_ctor_set_uint8(v___x_3063_, 4, v___x_3027_);
lean_ctor_set_uint8(v___x_3063_, 5, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 6, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 7, v___x_3027_);
lean_ctor_set_uint8(v___x_3063_, 8, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 9, v___x_3060_);
lean_ctor_set_uint8(v___x_3063_, 10, v___x_3061_);
lean_ctor_set_uint8(v___x_3063_, 11, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 12, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 13, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 14, v___x_3062_);
lean_ctor_set_uint8(v___x_3063_, 15, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 16, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 17, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 18, v___x_3044_);
lean_ctor_set_uint8(v___x_3063_, 19, v___x_3027_);
v___x_3064_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3063_);
v___x_3065_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set_uint64(v___x_3065_, sizeof(void*)*1, v___x_3064_);
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3068_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3069_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3070_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3071_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3071_, 0, v___x_3065_);
lean_ctor_set(v___x_3071_, 1, v___x_3002_);
lean_ctor_set(v___x_3071_, 2, v___x_3068_);
lean_ctor_set(v___x_3071_, 3, v___x_3069_);
lean_ctor_set(v___x_3071_, 4, v___x_3070_);
lean_ctor_set(v___x_3071_, 5, v___x_3066_);
lean_ctor_set(v___x_3071_, 6, v___x_3070_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*7, v___x_3027_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*7 + 1, v___x_3027_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*7 + 2, v___x_3027_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*7 + 3, v___x_3022_);
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3073_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3074_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3072_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
lean_ctor_set(v___x_3075_, 2, v___x_3002_);
lean_ctor_set(v___x_3075_, 3, v___x_3067_);
lean_ctor_set(v___x_3075_, 4, v___x_3074_);
v___x_3076_ = lean_st_mk_ref(v___x_3075_);
v___x_3077_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3017_, v___x_3022_, v___x_3071_, v___x_3076_, v___y_3005_, v___y_3006_);
lean_dec_ref_known(v___x_3071_, 7);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3079_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = lean_st_ref_get(v___x_3076_);
lean_dec(v___x_3076_);
lean_dec(v___x_3079_);
v_a_3046_ = v_a_3078_;
goto v___jp_3045_;
}
else
{
lean_dec(v___x_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3080_; 
v_a_3080_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3077_, 1);
v_a_3046_ = v_a_3080_;
goto v___jp_3045_;
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
v_a_3081_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3077_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3077_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
v___jp_3045_:
{
if (lean_obj_tag(v_a_3046_) == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_box(v___x_3027_);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
else
{
lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3056_; 
v_isSharedCheck_3056_ = !lean_is_exclusive(v_a_3046_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v_a_3046_, 0);
lean_dec(v_unused_3057_);
v___x_3050_ = v_a_3046_;
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
else
{
lean_dec(v_a_3046_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = lean_box(v___x_3044_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set_tag(v___x_3050_, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
else
{
uint8_t v___x_3089_; uint8_t v___x_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; uint64_t v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_dec(v_snd_3018_);
v___x_3089_ = 1;
v___x_3090_ = 0;
v___x_3091_ = 2;
v___x_3092_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3092_, 0, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3092_, 1, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3092_, 2, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3092_, 3, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3092_, 4, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3092_, 5, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 6, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 7, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3092_, 8, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 9, v___x_3089_);
lean_ctor_set_uint8(v___x_3092_, 10, v___x_3090_);
lean_ctor_set_uint8(v___x_3092_, 11, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 12, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 13, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 14, v___x_3091_);
lean_ctor_set_uint8(v___x_3092_, 15, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 16, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 17, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 18, v___x_3027_);
lean_ctor_set_uint8(v___x_3092_, 19, v_hasTrace_3009_);
v___x_3093_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3092_);
v___x_3094_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3094_, 0, v___x_3092_);
lean_ctor_set_uint64(v___x_3094_, sizeof(void*)*1, v___x_3093_);
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3097_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3098_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3099_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3100_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3100_, 0, v___x_3094_);
lean_ctor_set(v___x_3100_, 1, v___x_3002_);
lean_ctor_set(v___x_3100_, 2, v___x_3097_);
lean_ctor_set(v___x_3100_, 3, v___x_3098_);
lean_ctor_set(v___x_3100_, 4, v___x_3099_);
lean_ctor_set(v___x_3100_, 5, v___x_3095_);
lean_ctor_set(v___x_3100_, 6, v___x_3099_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*7, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*7 + 1, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*7 + 2, v_hasTrace_3009_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*7 + 3, v___x_3022_);
v___x_3101_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3102_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3103_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3101_);
lean_ctor_set(v___x_3104_, 1, v___x_3102_);
lean_ctor_set(v___x_3104_, 2, v___x_3002_);
lean_ctor_set(v___x_3104_, 3, v___x_3096_);
lean_ctor_set(v___x_3104_, 4, v___x_3103_);
v___x_3105_ = lean_st_mk_ref(v___x_3104_);
v___x_3106_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3017_, v___x_3100_, v___x_3105_, v___y_3005_, v___y_3006_);
lean_dec_ref_known(v___x_3100_, 7);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = lean_st_ref_get(v___x_3105_);
lean_dec(v___x_3105_);
lean_dec(v___x_3108_);
v_a_3029_ = v_a_3107_;
goto v___jp_3028_;
}
else
{
lean_dec(v___x_3105_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3109_; 
v_a_3109_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3106_, 1);
v_a_3029_ = v_a_3109_;
goto v___jp_3028_;
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_del_object(v___x_3015_);
v_a_3110_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3106_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3106_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
v___jp_3028_:
{
if (lean_obj_tag(v_a_3029_) == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3030_ = lean_box(v_hasTrace_3009_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set_tag(v___x_3015_, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3030_);
v___x_3032_ = v___x_3015_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
else
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3041_; 
lean_del_object(v___x_3015_);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_a_3029_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v_a_3029_, 0);
lean_dec(v_unused_3042_);
v___x_3035_ = v_a_3029_;
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v_a_3029_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = lean_box(v___x_3027_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set_tag(v___x_3035_, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3037_);
v___x_3039_ = v___x_3035_;
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
}
}
}
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec(v___x_3012_);
lean_dec(v_name_3004_);
lean_dec(v___x_3002_);
v___x_3119_ = lean_box(v_hasTrace_3009_);
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
return v___x_3120_;
}
}
else
{
lean_object* v_toCold_3121_; lean_object* v_inheritedTraceOptions_3122_; lean_object* v___f_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v_a_3131_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v_a_3146_; lean_object* v___y_3149_; lean_object* v___y_3150_; uint8_t v_a_3151_; uint8_t v___y_3155_; lean_object* v___y_3156_; uint8_t v___y_3157_; lean_object* v___y_3158_; lean_object* v_a_3159_; uint8_t v___y_3161_; lean_object* v___y_3162_; uint8_t v___y_3163_; lean_object* v___y_3164_; lean_object* v_a_3165_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v_a_3169_; lean_object* v___y_3179_; lean_object* v___y_3180_; uint8_t v_a_3181_; uint8_t v___y_3185_; uint8_t v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v_a_3189_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v_a_3194_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v_a_3199_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; 
v_toCold_3121_ = lean_ctor_get(v___y_3005_, 0);
v_inheritedTraceOptions_3122_ = lean_ctor_get(v_toCold_3121_, 4);
lean_inc(v_name_3004_);
v___f_3123_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3123_, 0, v_name_3004_);
v___x_3124_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3125_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3126_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3127_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3122_, v_options_3008_, v___x_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3336_ = l_Lean_trace_profiler;
v___x_3337_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3008_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; lean_object* v_env_3339_; lean_object* v___x_3340_; 
lean_dec_ref(v___f_3123_);
lean_dec_ref(v___f_3003_);
v___x_3338_ = lean_st_ref_get(v___y_3006_);
v_env_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc_ref(v_env_3339_);
lean_dec(v___x_3338_);
lean_inc(v_name_3004_);
v___x_3340_ = l_Lean_Meta_declFromEqLikeName(v_env_3339_, v_name_3004_);
if (lean_obj_tag(v___x_3340_) == 1)
{
lean_object* v_val_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3446_; 
v_val_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3446_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_val_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3446_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_fst_3345_; lean_object* v_snd_3346_; lean_object* v___x_3347_; lean_object* v_env_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; 
v_fst_3345_ = lean_ctor_get(v_val_3341_, 0);
lean_inc_n(v_fst_3345_, 2);
v_snd_3346_ = lean_ctor_get(v_val_3341_, 1);
lean_inc_n(v_snd_3346_, 2);
lean_dec(v_val_3341_);
v___x_3347_ = lean_st_ref_get(v___y_3006_);
v_env_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc_ref(v_env_3348_);
lean_dec(v___x_3347_);
v___x_3349_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3348_, v_fst_3345_, v_snd_3346_);
v___x_3350_ = lean_name_eq(v_name_3004_, v___x_3349_);
lean_dec(v___x_3349_);
lean_dec(v_name_3004_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
lean_dec(v_snd_3346_);
lean_dec(v_fst_3345_);
lean_dec(v___x_3002_);
v___x_3351_ = lean_box(v___x_3337_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set_tag(v___x_3343_, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3351_);
v___x_3353_ = v___x_3343_;
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
else
{
uint8_t v___x_3355_; lean_object* v_a_3357_; 
lean_inc(v_snd_3346_);
v___x_3355_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3346_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3371_; uint8_t v___x_3372_; lean_object* v_a_3374_; 
lean_del_object(v___x_3343_);
v___x_3371_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3372_ = lean_string_dec_eq(v_snd_3346_, v___x_3371_);
lean_dec(v_snd_3346_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec(v_fst_3345_);
lean_dec(v___x_3002_);
v___x_3386_ = lean_box(v___x_3337_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
return v___x_3387_;
}
else
{
uint8_t v___x_3388_; uint8_t v___x_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; uint64_t v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3388_ = 1;
v___x_3389_ = 0;
v___x_3390_ = 2;
v___x_3391_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3391_, 0, v___x_3355_);
lean_ctor_set_uint8(v___x_3391_, 1, v___x_3355_);
lean_ctor_set_uint8(v___x_3391_, 2, v___x_3355_);
lean_ctor_set_uint8(v___x_3391_, 3, v___x_3355_);
lean_ctor_set_uint8(v___x_3391_, 4, v___x_3355_);
lean_ctor_set_uint8(v___x_3391_, 5, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 6, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 7, v___x_3355_);
lean_ctor_set_uint8(v___x_3391_, 8, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 9, v___x_3388_);
lean_ctor_set_uint8(v___x_3391_, 10, v___x_3389_);
lean_ctor_set_uint8(v___x_3391_, 11, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 12, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 13, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 14, v___x_3390_);
lean_ctor_set_uint8(v___x_3391_, 15, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 16, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 17, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 18, v___x_3372_);
lean_ctor_set_uint8(v___x_3391_, 19, v___x_3355_);
v___x_3392_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3391_);
v___x_3393_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set_uint64(v___x_3393_, sizeof(void*)*1, v___x_3392_);
v___x_3394_ = lean_unsigned_to_nat(0u);
v___x_3395_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3396_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3397_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3398_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3399_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3399_, 0, v___x_3393_);
lean_ctor_set(v___x_3399_, 1, v___x_3002_);
lean_ctor_set(v___x_3399_, 2, v___x_3396_);
lean_ctor_set(v___x_3399_, 3, v___x_3397_);
lean_ctor_set(v___x_3399_, 4, v___x_3398_);
lean_ctor_set(v___x_3399_, 5, v___x_3394_);
lean_ctor_set(v___x_3399_, 6, v___x_3398_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7, v___x_3355_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 1, v___x_3355_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 2, v___x_3355_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 3, v_hasTrace_3009_);
v___x_3400_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3401_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3402_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3400_);
lean_ctor_set(v___x_3403_, 1, v___x_3401_);
lean_ctor_set(v___x_3403_, 2, v___x_3002_);
lean_ctor_set(v___x_3403_, 3, v___x_3395_);
lean_ctor_set(v___x_3403_, 4, v___x_3402_);
v___x_3404_ = lean_st_mk_ref(v___x_3403_);
v___x_3405_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3345_, v_hasTrace_3009_, v___x_3399_, v___x_3404_, v___y_3005_, v___y_3006_);
lean_dec_ref_known(v___x_3399_, 7);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = lean_st_ref_get(v___x_3404_);
lean_dec(v___x_3404_);
lean_dec(v___x_3407_);
v_a_3374_ = v_a_3406_;
goto v___jp_3373_;
}
else
{
lean_dec(v___x_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3405_, 1);
v_a_3374_ = v_a_3408_;
goto v___jp_3373_;
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_a_3409_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3405_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3405_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
v___jp_3373_:
{
if (lean_obj_tag(v_a_3374_) == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = lean_box(v___x_3355_);
v___x_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
return v___x_3376_;
}
else
{
lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3384_; 
v_isSharedCheck_3384_ = !lean_is_exclusive(v_a_3374_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; 
v_unused_3385_ = lean_ctor_get(v_a_3374_, 0);
lean_dec(v_unused_3385_);
v___x_3378_ = v_a_3374_;
v_isShared_3379_ = v_isSharedCheck_3384_;
goto v_resetjp_3377_;
}
else
{
lean_dec(v_a_3374_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3384_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3380_ = lean_box(v___x_3372_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3380_);
v___x_3382_ = v___x_3378_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
else
{
uint8_t v___x_3417_; uint8_t v___x_3418_; uint8_t v___x_3419_; lean_object* v___x_3420_; uint64_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v_snd_3346_);
v___x_3417_ = 1;
v___x_3418_ = 0;
v___x_3419_ = 2;
v___x_3420_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3420_, 0, v___x_3337_);
lean_ctor_set_uint8(v___x_3420_, 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3420_, 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3420_, 3, v___x_3337_);
lean_ctor_set_uint8(v___x_3420_, 4, v___x_3337_);
lean_ctor_set_uint8(v___x_3420_, 5, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 6, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 7, v___x_3337_);
lean_ctor_set_uint8(v___x_3420_, 8, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 9, v___x_3417_);
lean_ctor_set_uint8(v___x_3420_, 10, v___x_3418_);
lean_ctor_set_uint8(v___x_3420_, 11, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 12, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 13, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 14, v___x_3419_);
lean_ctor_set_uint8(v___x_3420_, 15, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 16, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 17, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 18, v___x_3355_);
lean_ctor_set_uint8(v___x_3420_, 19, v___x_3337_);
v___x_3421_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3420_);
v___x_3422_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set_uint64(v___x_3422_, sizeof(void*)*1, v___x_3421_);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3425_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3426_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3427_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3428_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3428_, 0, v___x_3422_);
lean_ctor_set(v___x_3428_, 1, v___x_3002_);
lean_ctor_set(v___x_3428_, 2, v___x_3425_);
lean_ctor_set(v___x_3428_, 3, v___x_3426_);
lean_ctor_set(v___x_3428_, 4, v___x_3427_);
lean_ctor_set(v___x_3428_, 5, v___x_3423_);
lean_ctor_set(v___x_3428_, 6, v___x_3427_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7, v___x_3337_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 1, v___x_3337_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 2, v___x_3337_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 3, v_hasTrace_3009_);
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3430_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3431_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
lean_ctor_set(v___x_3432_, 1, v___x_3430_);
lean_ctor_set(v___x_3432_, 2, v___x_3002_);
lean_ctor_set(v___x_3432_, 3, v___x_3424_);
lean_ctor_set(v___x_3432_, 4, v___x_3431_);
v___x_3433_ = lean_st_mk_ref(v___x_3432_);
v___x_3434_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3345_, v___x_3428_, v___x_3433_, v___y_3005_, v___y_3006_);
lean_dec_ref_known(v___x_3428_, 7);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = lean_st_ref_get(v___x_3433_);
lean_dec(v___x_3433_);
lean_dec(v___x_3436_);
v_a_3357_ = v_a_3435_;
goto v___jp_3356_;
}
else
{
lean_dec(v___x_3433_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3437_; 
v_a_3437_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3434_, 1);
v_a_3357_ = v_a_3437_;
goto v___jp_3356_;
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_del_object(v___x_3343_);
v_a_3438_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3434_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3434_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
v___jp_3356_:
{
if (lean_obj_tag(v_a_3357_) == 0)
{
lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3358_ = lean_box(v___x_3337_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set_tag(v___x_3343_, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3358_);
v___x_3360_ = v___x_3343_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
else
{
lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3369_; 
lean_del_object(v___x_3343_);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_a_3357_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; 
v_unused_3370_ = lean_ctor_get(v_a_3357_, 0);
lean_dec(v_unused_3370_);
v___x_3363_ = v_a_3357_;
v_isShared_3364_ = v_isSharedCheck_3369_;
goto v_resetjp_3362_;
}
else
{
lean_dec(v_a_3357_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3369_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___x_3367_; 
v___x_3365_ = lean_box(v___x_3355_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set_tag(v___x_3363_, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3365_);
v___x_3367_ = v___x_3363_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec(v___x_3340_);
lean_dec(v_name_3004_);
lean_dec(v___x_3002_);
v___x_3447_ = lean_box(v___x_3337_);
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
}
else
{
goto v___jp_3208_;
}
}
else
{
goto v___jp_3208_;
}
v___jp_3128_:
{
lean_object* v___x_3132_; double v___x_3133_; double v___x_3134_; double v___x_3135_; double v___x_3136_; double v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3132_ = lean_io_mono_nanos_now();
v___x_3133_ = lean_float_of_nat(v___y_3129_);
v___x_3134_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3135_ = lean_float_div(v___x_3133_, v___x_3134_);
v___x_3136_ = lean_float_of_nat(v___x_3132_);
v___x_3137_ = lean_float_div(v___x_3136_, v___x_3134_);
v___x_3138_ = lean_box_float(v___x_3135_);
v___x_3139_ = lean_box_float(v___x_3137_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v_a_3131_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3124_, v_hasTrace_3009_, v___x_3125_, v_options_3008_, v___x_3127_, v___y_3130_, v___f_3123_, v___x_3141_, v___y_3005_, v___y_3006_);
return v___x_3142_;
}
v___jp_3143_:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_a_3146_);
v___y_3129_ = v___y_3144_;
v___y_3130_ = v___y_3145_;
v_a_3131_ = v___x_3147_;
goto v___jp_3128_;
}
v___jp_3148_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_box(v_a_3151_);
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
v___y_3129_ = v___y_3149_;
v___y_3130_ = v___y_3150_;
v_a_3131_ = v___x_3153_;
goto v___jp_3128_;
}
v___jp_3154_:
{
if (lean_obj_tag(v_a_3159_) == 0)
{
v___y_3149_ = v___y_3156_;
v___y_3150_ = v___y_3158_;
v_a_3151_ = v___y_3157_;
goto v___jp_3148_;
}
else
{
lean_dec_ref_known(v_a_3159_, 1);
v___y_3149_ = v___y_3156_;
v___y_3150_ = v___y_3158_;
v_a_3151_ = v___y_3155_;
goto v___jp_3148_;
}
}
v___jp_3160_:
{
if (lean_obj_tag(v_a_3165_) == 0)
{
v___y_3149_ = v___y_3162_;
v___y_3150_ = v___y_3164_;
v_a_3151_ = v___y_3161_;
goto v___jp_3148_;
}
else
{
lean_dec_ref_known(v_a_3165_, 1);
v___y_3149_ = v___y_3162_;
v___y_3150_ = v___y_3164_;
v_a_3151_ = v___y_3163_;
goto v___jp_3148_;
}
}
v___jp_3166_:
{
lean_object* v___x_3170_; double v___x_3171_; double v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3170_ = lean_io_get_num_heartbeats();
v___x_3171_ = lean_float_of_nat(v___y_3168_);
v___x_3172_ = lean_float_of_nat(v___x_3170_);
v___x_3173_ = lean_box_float(v___x_3171_);
v___x_3174_ = lean_box_float(v___x_3172_);
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v_a_3169_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3124_, v_hasTrace_3009_, v___x_3125_, v_options_3008_, v___x_3127_, v___y_3167_, v___f_3123_, v___x_3176_, v___y_3005_, v___y_3006_);
return v___x_3177_;
}
v___jp_3178_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(v_a_3181_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
v___y_3167_ = v___y_3180_;
v___y_3168_ = v___y_3179_;
v_a_3169_ = v___x_3183_;
goto v___jp_3166_;
}
v___jp_3184_:
{
if (lean_obj_tag(v_a_3189_) == 0)
{
v___y_3179_ = v___y_3188_;
v___y_3180_ = v___y_3187_;
v_a_3181_ = v___y_3185_;
goto v___jp_3178_;
}
else
{
lean_dec_ref_known(v_a_3189_, 1);
v___y_3179_ = v___y_3188_;
v___y_3180_ = v___y_3187_;
v_a_3181_ = v___y_3186_;
goto v___jp_3178_;
}
}
v___jp_3190_:
{
if (lean_obj_tag(v_a_3194_) == 0)
{
uint8_t v___x_3195_; 
v___x_3195_ = 0;
v___y_3179_ = v___y_3193_;
v___y_3180_ = v___y_3192_;
v_a_3181_ = v___x_3195_;
goto v___jp_3178_;
}
else
{
lean_dec_ref_known(v_a_3194_, 1);
v___y_3179_ = v___y_3193_;
v___y_3180_ = v___y_3192_;
v_a_3181_ = v___y_3191_;
goto v___jp_3178_;
}
}
v___jp_3196_:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v_a_3199_);
v___y_3167_ = v___y_3198_;
v___y_3168_ = v___y_3197_;
v_a_3169_ = v___x_3200_;
goto v___jp_3166_;
}
v___jp_3201_:
{
if (lean_obj_tag(v___y_3204_) == 0)
{
lean_object* v_a_3205_; uint8_t v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___y_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___y_3204_, 1);
v___x_3206_ = lean_unbox(v_a_3205_);
lean_dec(v_a_3205_);
v___y_3179_ = v___y_3203_;
v___y_3180_ = v___y_3202_;
v_a_3181_ = v___x_3206_;
goto v___jp_3178_;
}
else
{
lean_object* v_a_3207_; 
v_a_3207_ = lean_ctor_get(v___y_3204_, 0);
lean_inc(v_a_3207_);
lean_dec_ref_known(v___y_3204_, 1);
v___y_3197_ = v___y_3203_;
v___y_3198_ = v___y_3202_;
v_a_3199_ = v_a_3207_;
goto v___jp_3196_;
}
}
v___jp_3208_:
{
lean_object* v___x_3209_; lean_object* v_a_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3209_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3006_);
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref(v___x_3209_);
v___x_3211_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3212_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3008_, v___x_3211_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v_env_3215_; lean_object* v___x_3216_; 
lean_dec_ref(v___f_3003_);
v___x_3213_ = lean_io_mono_nanos_now();
v___x_3214_ = lean_st_ref_get(v___y_3006_);
v_env_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc_ref(v_env_3215_);
lean_dec(v___x_3214_);
lean_inc(v_name_3004_);
v___x_3216_ = l_Lean_Meta_declFromEqLikeName(v_env_3215_, v_name_3004_);
if (lean_obj_tag(v___x_3216_) == 1)
{
lean_object* v_val_3217_; lean_object* v_fst_3218_; lean_object* v_snd_3219_; lean_object* v___x_3220_; lean_object* v_env_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v_val_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v___x_3216_, 1);
v_fst_3218_ = lean_ctor_get(v_val_3217_, 0);
lean_inc_n(v_fst_3218_, 2);
v_snd_3219_ = lean_ctor_get(v_val_3217_, 1);
lean_inc_n(v_snd_3219_, 2);
lean_dec(v_val_3217_);
v___x_3220_ = lean_st_ref_get(v___y_3006_);
v_env_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc_ref(v_env_3221_);
lean_dec(v___x_3220_);
v___x_3222_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3221_, v_fst_3218_, v_snd_3219_);
v___x_3223_ = lean_name_eq(v_name_3004_, v___x_3222_);
lean_dec(v___x_3222_);
lean_dec(v_name_3004_);
if (v___x_3223_ == 0)
{
lean_dec(v_snd_3219_);
lean_dec(v_fst_3218_);
lean_dec(v___x_3002_);
v___y_3149_ = v___x_3213_;
v___y_3150_ = v_a_3210_;
v_a_3151_ = v___x_3212_;
goto v___jp_3148_;
}
else
{
uint8_t v___x_3224_; 
lean_inc(v_snd_3219_);
v___x_3224_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3219_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; uint8_t v___x_3226_; 
v___x_3225_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3226_ = lean_string_dec_eq(v_snd_3219_, v___x_3225_);
lean_dec(v_snd_3219_);
if (v___x_3226_ == 0)
{
lean_dec(v_fst_3218_);
lean_dec(v___x_3002_);
v___y_3149_ = v___x_3213_;
v___y_3150_ = v_a_3210_;
v_a_3151_ = v___x_3212_;
goto v___jp_3148_;
}
else
{
uint8_t v___x_3227_; uint8_t v___x_3228_; uint8_t v___x_3229_; lean_object* v___x_3230_; uint64_t v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3227_ = 1;
v___x_3228_ = 0;
v___x_3229_ = 2;
v___x_3230_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3230_, 0, v___x_3224_);
lean_ctor_set_uint8(v___x_3230_, 1, v___x_3224_);
lean_ctor_set_uint8(v___x_3230_, 2, v___x_3224_);
lean_ctor_set_uint8(v___x_3230_, 3, v___x_3224_);
lean_ctor_set_uint8(v___x_3230_, 4, v___x_3224_);
lean_ctor_set_uint8(v___x_3230_, 5, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 6, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 7, v___x_3224_);
lean_ctor_set_uint8(v___x_3230_, 8, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 9, v___x_3227_);
lean_ctor_set_uint8(v___x_3230_, 10, v___x_3228_);
lean_ctor_set_uint8(v___x_3230_, 11, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 12, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 13, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 14, v___x_3229_);
lean_ctor_set_uint8(v___x_3230_, 15, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 16, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 17, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 18, v___x_3226_);
lean_ctor_set_uint8(v___x_3230_, 19, v___x_3224_);
v___x_3231_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3230_);
v___x_3232_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set_uint64(v___x_3232_, sizeof(void*)*1, v___x_3231_);
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3235_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3236_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3237_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3238_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3238_, 0, v___x_3232_);
lean_ctor_set(v___x_3238_, 1, v___x_3002_);
lean_ctor_set(v___x_3238_, 2, v___x_3235_);
lean_ctor_set(v___x_3238_, 3, v___x_3236_);
lean_ctor_set(v___x_3238_, 4, v___x_3237_);
lean_ctor_set(v___x_3238_, 5, v___x_3233_);
lean_ctor_set(v___x_3238_, 6, v___x_3237_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*7, v___x_3224_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*7 + 1, v___x_3224_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*7 + 2, v___x_3224_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*7 + 3, v_hasTrace_3009_);
v___x_3239_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3240_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3241_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3239_);
lean_ctor_set(v___x_3242_, 1, v___x_3240_);
lean_ctor_set(v___x_3242_, 2, v___x_3002_);
lean_ctor_set(v___x_3242_, 3, v___x_3234_);
lean_ctor_set(v___x_3242_, 4, v___x_3241_);
v___x_3243_ = lean_st_mk_ref(v___x_3242_);
v___x_3244_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3218_, v_hasTrace_3009_, v___x_3238_, v___x_3243_, v___y_3005_, v___y_3006_);
lean_dec_ref_known(v___x_3238_, 7);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 1);
v___x_3246_ = lean_st_ref_get(v___x_3243_);
lean_dec(v___x_3243_);
lean_dec(v___x_3246_);
v___y_3161_ = v___x_3224_;
v___y_3162_ = v___x_3213_;
v___y_3163_ = v___x_3226_;
v___y_3164_ = v_a_3210_;
v_a_3165_ = v_a_3245_;
goto v___jp_3160_;
}
else
{
lean_dec(v___x_3243_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3247_; 
v_a_3247_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3244_, 1);
v___y_3161_ = v___x_3224_;
v___y_3162_ = v___x_3213_;
v___y_3163_ = v___x_3226_;
v___y_3164_ = v_a_3210_;
v_a_3165_ = v_a_3247_;
goto v___jp_3160_;
}
else
{
lean_object* v_a_3248_; 
v_a_3248_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3244_, 1);
v___y_3144_ = v___x_3213_;
v___y_3145_ = v_a_3210_;
v_a_3146_ = v_a_3248_;
goto v___jp_3143_;
}
}
}
}
else
{
uint8_t v___x_3249_; uint8_t v___x_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; uint64_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec(v_snd_3219_);
v___x_3249_ = 1;
v___x_3250_ = 0;
v___x_3251_ = 2;
v___x_3252_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3252_, 0, v___x_3212_);
lean_ctor_set_uint8(v___x_3252_, 1, v___x_3212_);
lean_ctor_set_uint8(v___x_3252_, 2, v___x_3212_);
lean_ctor_set_uint8(v___x_3252_, 3, v___x_3212_);
lean_ctor_set_uint8(v___x_3252_, 4, v___x_3212_);
lean_ctor_set_uint8(v___x_3252_, 5, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 6, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 7, v___x_3212_);
lean_ctor_set_uint8(v___x_3252_, 8, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 9, v___x_3249_);
lean_ctor_set_uint8(v___x_3252_, 10, v___x_3250_);
lean_ctor_set_uint8(v___x_3252_, 11, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 12, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 13, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 14, v___x_3251_);
lean_ctor_set_uint8(v___x_3252_, 15, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 16, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 17, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 18, v___x_3224_);
lean_ctor_set_uint8(v___x_3252_, 19, v___x_3212_);
v___x_3253_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3252_);
v___x_3254_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set_uint64(v___x_3254_, sizeof(void*)*1, v___x_3253_);
v___x_3255_ = lean_unsigned_to_nat(0u);
v___x_3256_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3257_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3258_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3259_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3260_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3260_, 0, v___x_3254_);
lean_ctor_set(v___x_3260_, 1, v___x_3002_);
lean_ctor_set(v___x_3260_, 2, v___x_3257_);
lean_ctor_set(v___x_3260_, 3, v___x_3258_);
lean_ctor_set(v___x_3260_, 4, v___x_3259_);
lean_ctor_set(v___x_3260_, 5, v___x_3255_);
lean_ctor_set(v___x_3260_, 6, v___x_3259_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*7, v___x_3212_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*7 + 1, v___x_3212_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*7 + 2, v___x_3212_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*7 + 3, v_hasTrace_3009_);
v___x_3261_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3262_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3263_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3261_);
lean_ctor_set(v___x_3264_, 1, v___x_3262_);
lean_ctor_set(v___x_3264_, 2, v___x_3002_);
lean_ctor_set(v___x_3264_, 3, v___x_3256_);
lean_ctor_set(v___x_3264_, 4, v___x_3263_);
v___x_3265_ = lean_st_mk_ref(v___x_3264_);
v___x_3266_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3218_, v___x_3260_, v___x_3265_, v___y_3005_, v___y_3006_);
lean_dec_ref_known(v___x_3260_, 7);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3268_ = lean_st_ref_get(v___x_3265_);
lean_dec(v___x_3265_);
lean_dec(v___x_3268_);
v___y_3155_ = v___x_3224_;
v___y_3156_ = v___x_3213_;
v___y_3157_ = v___x_3212_;
v___y_3158_ = v_a_3210_;
v_a_3159_ = v_a_3267_;
goto v___jp_3154_;
}
else
{
lean_dec(v___x_3265_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3269_; 
v_a_3269_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3266_, 1);
v___y_3155_ = v___x_3224_;
v___y_3156_ = v___x_3213_;
v___y_3157_ = v___x_3212_;
v___y_3158_ = v_a_3210_;
v_a_3159_ = v_a_3269_;
goto v___jp_3154_;
}
else
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3266_, 1);
v___y_3144_ = v___x_3213_;
v___y_3145_ = v_a_3210_;
v_a_3146_ = v_a_3270_;
goto v___jp_3143_;
}
}
}
}
}
else
{
lean_dec(v___x_3216_);
lean_dec(v_name_3004_);
lean_dec(v___x_3002_);
v___y_3149_ = v___x_3213_;
v___y_3150_ = v_a_3210_;
v_a_3151_ = v___x_3212_;
goto v___jp_3148_;
}
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v_env_3273_; lean_object* v___x_3274_; 
v___x_3271_ = lean_io_get_num_heartbeats();
v___x_3272_ = lean_st_ref_get(v___y_3006_);
v_env_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc_ref(v_env_3273_);
lean_dec(v___x_3272_);
lean_inc(v_name_3004_);
v___x_3274_ = l_Lean_Meta_declFromEqLikeName(v_env_3273_, v_name_3004_);
if (lean_obj_tag(v___x_3274_) == 1)
{
lean_object* v_val_3275_; lean_object* v_fst_3276_; lean_object* v_snd_3277_; lean_object* v___x_3278_; lean_object* v_env_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; 
v_val_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_val_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v_fst_3276_ = lean_ctor_get(v_val_3275_, 0);
lean_inc_n(v_fst_3276_, 2);
v_snd_3277_ = lean_ctor_get(v_val_3275_, 1);
lean_inc_n(v_snd_3277_, 2);
lean_dec(v_val_3275_);
v___x_3278_ = lean_st_ref_get(v___y_3006_);
v_env_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc_ref(v_env_3279_);
lean_dec(v___x_3278_);
v___x_3280_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3279_, v_fst_3276_, v_snd_3277_);
v___x_3281_ = lean_name_eq(v_name_3004_, v___x_3280_);
lean_dec(v___x_3280_);
lean_dec(v_name_3004_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec(v_snd_3277_);
lean_dec(v_fst_3276_);
lean_dec(v___x_3002_);
v___x_3282_ = lean_box(0);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
v___x_3283_ = lean_apply_4(v___f_3003_, v___x_3282_, v___y_3005_, v___y_3006_, lean_box(0));
v___y_3202_ = v_a_3210_;
v___y_3203_ = v___x_3271_;
v___y_3204_ = v___x_3283_;
goto v___jp_3201_;
}
else
{
uint8_t v___x_3284_; 
lean_inc(v_snd_3277_);
v___x_3284_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3277_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3286_ = lean_string_dec_eq(v_snd_3277_, v___x_3285_);
lean_dec(v_snd_3277_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_dec(v_fst_3276_);
lean_dec(v___x_3002_);
v___x_3287_ = lean_box(0);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
v___x_3288_ = lean_apply_4(v___f_3003_, v___x_3287_, v___y_3005_, v___y_3006_, lean_box(0));
v___y_3202_ = v_a_3210_;
v___y_3203_ = v___x_3271_;
v___y_3204_ = v___x_3288_;
goto v___jp_3201_;
}
else
{
uint8_t v___x_3289_; uint8_t v___x_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; uint64_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec_ref(v___f_3003_);
v___x_3289_ = 1;
v___x_3290_ = 0;
v___x_3291_ = 2;
v___x_3292_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3292_, 0, v___x_3284_);
lean_ctor_set_uint8(v___x_3292_, 1, v___x_3284_);
lean_ctor_set_uint8(v___x_3292_, 2, v___x_3284_);
lean_ctor_set_uint8(v___x_3292_, 3, v___x_3284_);
lean_ctor_set_uint8(v___x_3292_, 4, v___x_3284_);
lean_ctor_set_uint8(v___x_3292_, 5, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 6, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 7, v___x_3284_);
lean_ctor_set_uint8(v___x_3292_, 8, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 9, v___x_3289_);
lean_ctor_set_uint8(v___x_3292_, 10, v___x_3290_);
lean_ctor_set_uint8(v___x_3292_, 11, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 12, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 13, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 14, v___x_3291_);
lean_ctor_set_uint8(v___x_3292_, 15, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 16, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 17, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 18, v___x_3286_);
lean_ctor_set_uint8(v___x_3292_, 19, v___x_3284_);
v___x_3293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3292_);
v___x_3294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set_uint64(v___x_3294_, sizeof(void*)*1, v___x_3293_);
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3297_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3298_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3299_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3300_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3300_, 0, v___x_3294_);
lean_ctor_set(v___x_3300_, 1, v___x_3002_);
lean_ctor_set(v___x_3300_, 2, v___x_3297_);
lean_ctor_set(v___x_3300_, 3, v___x_3298_);
lean_ctor_set(v___x_3300_, 4, v___x_3299_);
lean_ctor_set(v___x_3300_, 5, v___x_3295_);
lean_ctor_set(v___x_3300_, 6, v___x_3299_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7, v___x_3284_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 1, v___x_3284_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 2, v___x_3284_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*7 + 3, v___x_3212_);
v___x_3301_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3302_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3303_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3301_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
lean_ctor_set(v___x_3304_, 2, v___x_3002_);
lean_ctor_set(v___x_3304_, 3, v___x_3296_);
lean_ctor_set(v___x_3304_, 4, v___x_3303_);
v___x_3305_ = lean_st_mk_ref(v___x_3304_);
v___x_3306_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3276_, v___x_3212_, v___x_3300_, v___x_3305_, v___y_3005_, v___y_3006_);
lean_dec_ref_known(v___x_3300_, 7);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = lean_st_ref_get(v___x_3305_);
lean_dec(v___x_3305_);
lean_dec(v___x_3308_);
v___y_3185_ = v___x_3284_;
v___y_3186_ = v___x_3286_;
v___y_3187_ = v_a_3210_;
v___y_3188_ = v___x_3271_;
v_a_3189_ = v_a_3307_;
goto v___jp_3184_;
}
else
{
lean_dec(v___x_3305_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3309_; 
v_a_3309_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3306_, 1);
v___y_3185_ = v___x_3284_;
v___y_3186_ = v___x_3286_;
v___y_3187_ = v_a_3210_;
v___y_3188_ = v___x_3271_;
v_a_3189_ = v_a_3309_;
goto v___jp_3184_;
}
else
{
lean_object* v_a_3310_; 
v_a_3310_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3306_, 1);
v___y_3197_ = v___x_3271_;
v___y_3198_ = v_a_3210_;
v_a_3199_ = v_a_3310_;
goto v___jp_3196_;
}
}
}
}
else
{
uint8_t v___x_3311_; uint8_t v___x_3312_; uint8_t v___x_3313_; uint8_t v___x_3314_; lean_object* v___x_3315_; uint64_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec(v_snd_3277_);
lean_dec_ref(v___f_3003_);
v___x_3311_ = 0;
v___x_3312_ = 1;
v___x_3313_ = 0;
v___x_3314_ = 2;
v___x_3315_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3315_, 0, v___x_3311_);
lean_ctor_set_uint8(v___x_3315_, 1, v___x_3311_);
lean_ctor_set_uint8(v___x_3315_, 2, v___x_3311_);
lean_ctor_set_uint8(v___x_3315_, 3, v___x_3311_);
lean_ctor_set_uint8(v___x_3315_, 4, v___x_3311_);
lean_ctor_set_uint8(v___x_3315_, 5, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 6, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 7, v___x_3311_);
lean_ctor_set_uint8(v___x_3315_, 8, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 9, v___x_3312_);
lean_ctor_set_uint8(v___x_3315_, 10, v___x_3313_);
lean_ctor_set_uint8(v___x_3315_, 11, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 12, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 13, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 14, v___x_3314_);
lean_ctor_set_uint8(v___x_3315_, 15, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 16, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 17, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 18, v___x_3284_);
lean_ctor_set_uint8(v___x_3315_, 19, v___x_3311_);
v___x_3316_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3315_);
v___x_3317_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set_uint64(v___x_3317_, sizeof(void*)*1, v___x_3316_);
v___x_3318_ = lean_unsigned_to_nat(0u);
v___x_3319_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3320_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3321_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3322_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3323_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3323_, 0, v___x_3317_);
lean_ctor_set(v___x_3323_, 1, v___x_3002_);
lean_ctor_set(v___x_3323_, 2, v___x_3320_);
lean_ctor_set(v___x_3323_, 3, v___x_3321_);
lean_ctor_set(v___x_3323_, 4, v___x_3322_);
lean_ctor_set(v___x_3323_, 5, v___x_3318_);
lean_ctor_set(v___x_3323_, 6, v___x_3322_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*7, v___x_3311_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*7 + 1, v___x_3311_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*7 + 2, v___x_3311_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*7 + 3, v___x_3212_);
v___x_3324_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3325_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3326_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3324_);
lean_ctor_set(v___x_3327_, 1, v___x_3325_);
lean_ctor_set(v___x_3327_, 2, v___x_3002_);
lean_ctor_set(v___x_3327_, 3, v___x_3319_);
lean_ctor_set(v___x_3327_, 4, v___x_3326_);
v___x_3328_ = lean_st_mk_ref(v___x_3327_);
v___x_3329_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3276_, v___x_3323_, v___x_3328_, v___y_3005_, v___y_3006_);
lean_dec_ref_known(v___x_3323_, 7);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v___x_3331_ = lean_st_ref_get(v___x_3328_);
lean_dec(v___x_3328_);
lean_dec(v___x_3331_);
v___y_3191_ = v___x_3284_;
v___y_3192_ = v_a_3210_;
v___y_3193_ = v___x_3271_;
v_a_3194_ = v_a_3330_;
goto v___jp_3190_;
}
else
{
lean_dec(v___x_3328_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3332_; 
v_a_3332_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3329_, 1);
v___y_3191_ = v___x_3284_;
v___y_3192_ = v_a_3210_;
v___y_3193_ = v___x_3271_;
v_a_3194_ = v_a_3332_;
goto v___jp_3190_;
}
else
{
lean_object* v_a_3333_; 
v_a_3333_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3329_, 1);
v___y_3197_ = v___x_3271_;
v___y_3198_ = v_a_3210_;
v_a_3199_ = v_a_3333_;
goto v___jp_3196_;
}
}
}
}
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec(v___x_3274_);
lean_dec(v_name_3004_);
lean_dec(v___x_3002_);
v___x_3334_ = lean_box(0);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
v___x_3335_ = lean_apply_4(v___f_3003_, v___x_3334_, v___y_3005_, v___y_3006_, lean_box(0));
v___y_3202_ = v_a_3210_;
v___y_3203_ = v___x_3271_;
v___y_3204_ = v___x_3335_;
goto v___jp_3201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3449_, lean_object* v___f_3450_, lean_object* v_name_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3449_, v___f_3450_, v_name_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
return v_res_3455_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = lean_unsigned_to_nat(3137104340u);
v___x_3501_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3502_ = l_Lean_Name_num___override(v___x_3501_, v___x_3500_);
return v___x_3502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3505_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3506_ = l_Lean_Name_str___override(v___x_3505_, v___x_3504_);
return v___x_3506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3509_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3510_ = l_Lean_Name_str___override(v___x_3509_, v___x_3508_);
return v___x_3510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = lean_unsigned_to_nat(2u);
v___x_3512_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3513_ = l_Lean_Name_num___override(v___x_3512_, v___x_3511_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3515_; lean_object* v___x_3516_; 
v___f_3515_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3516_ = l_Lean_registerReservedNameAction(v___f_3515_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3517_; uint8_t v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_dec_ref_known(v___x_3516_, 1);
v___x_3517_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3518_ = 0;
v___x_3519_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3520_ = l_Lean_registerTraceClass(v___x_3517_, v___x_3518_, v___x_3519_);
return v___x_3520_;
}
else
{
return v___x_3516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3523_, lean_object* v_x_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3524_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3529_, lean_object* v_x_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3529_, v_x_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3534_;
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
