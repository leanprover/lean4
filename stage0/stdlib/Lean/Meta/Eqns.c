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
v_options_315_ = lean_ctor_get(v___y_310_, 2);
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
v_ref_330_ = lean_ctor_get(v___y_327_, 5);
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
lean_object* v___y_677_; uint8_t v___y_678_; lean_object* v_fileName_679_; lean_object* v_fileMap_680_; lean_object* v_currRecDepth_681_; lean_object* v_ref_682_; lean_object* v_currNamespace_683_; lean_object* v_openDecls_684_; lean_object* v_initHeartbeats_685_; lean_object* v_maxHeartbeats_686_; lean_object* v_quotContext_687_; lean_object* v_currMacroScope_688_; lean_object* v_cancelTk_x3f_689_; uint8_t v_suppressElabErrors_690_; lean_object* v_inheritedTraceOptions_691_; lean_object* v___y_692_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_env_699_; lean_object* v___x_700_; lean_object* v_toEnvExtension_701_; lean_object* v_asyncMode_702_; lean_object* v_fileName_703_; lean_object* v_fileMap_704_; lean_object* v_options_705_; lean_object* v_currRecDepth_706_; lean_object* v_ref_707_; lean_object* v_currNamespace_708_; lean_object* v_openDecls_709_; lean_object* v_initHeartbeats_710_; lean_object* v_maxHeartbeats_711_; lean_object* v_quotContext_712_; lean_object* v_currMacroScope_713_; lean_object* v_cancelTk_x3f_714_; uint8_t v_suppressElabErrors_715_; lean_object* v_inheritedTraceOptions_716_; lean_object* v___y_718_; uint8_t v___y_719_; uint8_t v___y_720_; lean_object* v___y_742_; lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___x_749_; 
v___x_697_ = lean_st_ref_get(v_a_674_);
v___x_698_ = lean_st_ref_get(v_a_674_);
v_env_699_ = lean_ctor_get(v___x_697_, 0);
lean_inc_ref(v_env_699_);
lean_dec(v___x_697_);
v___x_700_ = l_Lean_Meta_eqnOptionsExt;
v_toEnvExtension_701_ = lean_ctor_get(v___x_700_, 0);
v_asyncMode_702_ = lean_ctor_get(v_toEnvExtension_701_, 2);
v_fileName_703_ = lean_ctor_get(v_a_673_, 0);
v_fileMap_704_ = lean_ctor_get(v_a_673_, 1);
v_options_705_ = lean_ctor_get(v_a_673_, 2);
v_currRecDepth_706_ = lean_ctor_get(v_a_673_, 3);
v_ref_707_ = lean_ctor_get(v_a_673_, 5);
v_currNamespace_708_ = lean_ctor_get(v_a_673_, 6);
v_openDecls_709_ = lean_ctor_get(v_a_673_, 7);
v_initHeartbeats_710_ = lean_ctor_get(v_a_673_, 8);
v_maxHeartbeats_711_ = lean_ctor_get(v_a_673_, 9);
v_quotContext_712_ = lean_ctor_get(v_a_673_, 10);
v_currMacroScope_713_ = lean_ctor_get(v_a_673_, 11);
v_cancelTk_x3f_714_ = lean_ctor_get(v_a_673_, 12);
v_suppressElabErrors_715_ = lean_ctor_get_uint8(v_a_673_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_716_ = lean_ctor_get(v_a_673_, 13);
v___x_747_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__3, &l_Lean_Meta_withEqnOptions___redArg___closed__3_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__3);
v___x_748_ = 0;
v___x_749_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_747_, v___x_700_, v_env_699_, v_declName_669_, v_asyncMode_702_, v___x_748_);
if (lean_obj_tag(v___x_749_) == 1)
{
lean_object* v_val_750_; lean_object* v___y_752_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_val_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_756_ = l_Lean_Meta_eqnAffectingOptions;
v___x_757_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_757_ == 0)
{
lean_inc_ref(v_options_705_);
v___y_752_ = v_options_705_;
goto v___jp_751_;
}
else
{
uint8_t v___x_758_; 
v___x_758_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_758_ == 0)
{
if (v___x_757_ == 0)
{
lean_inc_ref(v_options_705_);
v___y_752_ = v_options_705_;
goto v___jp_751_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_705_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_756_, v___x_759_, v___x_760_, v_options_705_);
v___y_752_ = v___x_761_;
goto v___jp_751_;
}
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_705_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_756_, v___x_762_, v___x_763_, v_options_705_);
v___y_752_ = v___x_764_;
goto v___jp_751_;
}
}
v___jp_751_:
{
size_t v_sz_753_; size_t v___x_754_; lean_object* v___x_755_; 
v_sz_753_ = lean_array_size(v_val_750_);
v___x_754_ = ((size_t)0ULL);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_750_, v_sz_753_, v___x_754_, v___y_752_);
lean_dec(v_val_750_);
v___y_742_ = v___x_755_;
goto v___jp_741_;
}
}
else
{
lean_object* v___x_765_; uint8_t v___x_766_; 
lean_dec(v___x_749_);
v___x_765_ = l_Lean_Meta_eqnAffectingOptions;
v___x_766_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__5, &l_Lean_Meta_withEqnOptions___redArg___closed__5_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__5);
if (v___x_766_ == 0)
{
lean_inc_ref(v_options_705_);
v___y_742_ = v_options_705_;
goto v___jp_741_;
}
else
{
uint8_t v___x_767_; 
v___x_767_ = lean_uint8_once(&l_Lean_Meta_withEqnOptions___redArg___closed__6, &l_Lean_Meta_withEqnOptions___redArg___closed__6_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__6);
if (v___x_767_ == 0)
{
if (v___x_766_ == 0)
{
lean_inc_ref(v_options_705_);
v___y_742_ = v_options_705_;
goto v___jp_741_;
}
else
{
size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; 
v___x_768_ = ((size_t)0ULL);
v___x_769_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_705_);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_765_, v___x_768_, v___x_769_, v_options_705_);
v___y_742_ = v___x_770_;
goto v___jp_741_;
}
}
else
{
size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_771_ = ((size_t)0ULL);
v___x_772_ = lean_usize_once(&l_Lean_Meta_withEqnOptions___redArg___closed__7, &l_Lean_Meta_withEqnOptions___redArg___closed__7_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__7);
lean_inc_ref(v_options_705_);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_765_, v___x_771_, v___x_772_, v_options_705_);
v___y_742_ = v___x_773_;
goto v___jp_741_;
}
}
}
v___jp_676_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = l_Lean_maxRecDepth;
v___x_694_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v___y_677_, v___x_693_);
lean_inc_ref(v_inheritedTraceOptions_691_);
lean_inc(v_cancelTk_x3f_689_);
lean_inc(v_currMacroScope_688_);
lean_inc(v_quotContext_687_);
lean_inc(v_maxHeartbeats_686_);
lean_inc(v_initHeartbeats_685_);
lean_inc(v_openDecls_684_);
lean_inc(v_currNamespace_683_);
lean_inc(v_ref_682_);
lean_inc(v_currRecDepth_681_);
lean_inc_ref(v_fileMap_680_);
lean_inc_ref(v_fileName_679_);
v___x_695_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_695_, 0, v_fileName_679_);
lean_ctor_set(v___x_695_, 1, v_fileMap_680_);
lean_ctor_set(v___x_695_, 2, v___y_677_);
lean_ctor_set(v___x_695_, 3, v_currRecDepth_681_);
lean_ctor_set(v___x_695_, 4, v___x_694_);
lean_ctor_set(v___x_695_, 5, v_ref_682_);
lean_ctor_set(v___x_695_, 6, v_currNamespace_683_);
lean_ctor_set(v___x_695_, 7, v_openDecls_684_);
lean_ctor_set(v___x_695_, 8, v_initHeartbeats_685_);
lean_ctor_set(v___x_695_, 9, v_maxHeartbeats_686_);
lean_ctor_set(v___x_695_, 10, v_quotContext_687_);
lean_ctor_set(v___x_695_, 11, v_currMacroScope_688_);
lean_ctor_set(v___x_695_, 12, v_cancelTk_x3f_689_);
lean_ctor_set(v___x_695_, 13, v_inheritedTraceOptions_691_);
lean_ctor_set_uint8(v___x_695_, sizeof(void*)*14, v___y_678_);
lean_ctor_set_uint8(v___x_695_, sizeof(void*)*14 + 1, v_suppressElabErrors_690_);
lean_inc(v___y_692_);
lean_inc(v_a_672_);
lean_inc_ref(v_a_671_);
v___x_696_ = lean_apply_5(v_act_670_, v_a_671_, v_a_672_, v___x_695_, v___y_692_, lean_box(0));
return v___x_696_;
}
v___jp_717_:
{
if (v___y_720_ == 0)
{
lean_object* v___x_721_; lean_object* v_env_722_; lean_object* v_nextMacroScope_723_; lean_object* v_ngen_724_; lean_object* v_auxDeclNGen_725_; lean_object* v_traceState_726_; lean_object* v_messages_727_; lean_object* v_infoState_728_; lean_object* v_snapshotTasks_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_739_; 
v___x_721_ = lean_st_ref_take(v_a_674_);
v_env_722_ = lean_ctor_get(v___x_721_, 0);
v_nextMacroScope_723_ = lean_ctor_get(v___x_721_, 1);
v_ngen_724_ = lean_ctor_get(v___x_721_, 2);
v_auxDeclNGen_725_ = lean_ctor_get(v___x_721_, 3);
v_traceState_726_ = lean_ctor_get(v___x_721_, 4);
v_messages_727_ = lean_ctor_get(v___x_721_, 6);
v_infoState_728_ = lean_ctor_get(v___x_721_, 7);
v_snapshotTasks_729_ = lean_ctor_get(v___x_721_, 8);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v___x_721_, 5);
lean_dec(v_unused_740_);
v___x_731_ = v___x_721_;
v_isShared_732_ = v_isSharedCheck_739_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snapshotTasks_729_);
lean_inc(v_infoState_728_);
lean_inc(v_messages_727_);
lean_inc(v_traceState_726_);
lean_inc(v_auxDeclNGen_725_);
lean_inc(v_ngen_724_);
lean_inc(v_nextMacroScope_723_);
lean_inc(v_env_722_);
lean_dec(v___x_721_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_739_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_733_ = l_Lean_Kernel_enableDiag(v_env_722_, v___y_719_);
v___x_734_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 5, v___x_734_);
lean_ctor_set(v___x_731_, 0, v___x_733_);
v___x_736_ = v___x_731_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_nextMacroScope_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_ngen_724_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_auxDeclNGen_725_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_traceState_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 5, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_738_, 6, v_messages_727_);
lean_ctor_set(v_reuseFailAlloc_738_, 7, v_infoState_728_);
lean_ctor_set(v_reuseFailAlloc_738_, 8, v_snapshotTasks_729_);
v___x_736_ = v_reuseFailAlloc_738_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; 
v___x_737_ = lean_st_ref_put(v_a_674_, v___x_736_);
v___y_677_ = v___y_718_;
v___y_678_ = v___y_719_;
v_fileName_679_ = v_fileName_703_;
v_fileMap_680_ = v_fileMap_704_;
v_currRecDepth_681_ = v_currRecDepth_706_;
v_ref_682_ = v_ref_707_;
v_currNamespace_683_ = v_currNamespace_708_;
v_openDecls_684_ = v_openDecls_709_;
v_initHeartbeats_685_ = v_initHeartbeats_710_;
v_maxHeartbeats_686_ = v_maxHeartbeats_711_;
v_quotContext_687_ = v_quotContext_712_;
v_currMacroScope_688_ = v_currMacroScope_713_;
v_cancelTk_x3f_689_ = v_cancelTk_x3f_714_;
v_suppressElabErrors_690_ = v_suppressElabErrors_715_;
v_inheritedTraceOptions_691_ = v_inheritedTraceOptions_716_;
v___y_692_ = v_a_674_;
goto v___jp_676_;
}
}
}
else
{
v___y_677_ = v___y_718_;
v___y_678_ = v___y_719_;
v_fileName_679_ = v_fileName_703_;
v_fileMap_680_ = v_fileMap_704_;
v_currRecDepth_681_ = v_currRecDepth_706_;
v_ref_682_ = v_ref_707_;
v_currNamespace_683_ = v_currNamespace_708_;
v_openDecls_684_ = v_openDecls_709_;
v_initHeartbeats_685_ = v_initHeartbeats_710_;
v_maxHeartbeats_686_ = v_maxHeartbeats_711_;
v_quotContext_687_ = v_quotContext_712_;
v_currMacroScope_688_ = v_currMacroScope_713_;
v_cancelTk_x3f_689_ = v_cancelTk_x3f_714_;
v_suppressElabErrors_690_ = v_suppressElabErrors_715_;
v_inheritedTraceOptions_691_ = v_inheritedTraceOptions_716_;
v___y_692_ = v_a_674_;
goto v___jp_676_;
}
}
v___jp_741_:
{
lean_object* v_env_743_; lean_object* v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; 
v_env_743_ = lean_ctor_get(v___x_698_, 0);
lean_inc_ref(v_env_743_);
lean_dec(v___x_698_);
v___x_744_ = l_Lean_diagnostics;
v___x_745_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___y_742_, v___x_744_);
v___x_746_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_743_);
lean_dec_ref(v_env_743_);
if (v___x_745_ == 0)
{
if (v___x_746_ == 0)
{
v___y_677_ = v___y_742_;
v___y_678_ = v___x_745_;
v_fileName_679_ = v_fileName_703_;
v_fileMap_680_ = v_fileMap_704_;
v_currRecDepth_681_ = v_currRecDepth_706_;
v_ref_682_ = v_ref_707_;
v_currNamespace_683_ = v_currNamespace_708_;
v_openDecls_684_ = v_openDecls_709_;
v_initHeartbeats_685_ = v_initHeartbeats_710_;
v_maxHeartbeats_686_ = v_maxHeartbeats_711_;
v_quotContext_687_ = v_quotContext_712_;
v_currMacroScope_688_ = v_currMacroScope_713_;
v_cancelTk_x3f_689_ = v_cancelTk_x3f_714_;
v_suppressElabErrors_690_ = v_suppressElabErrors_715_;
v_inheritedTraceOptions_691_ = v_inheritedTraceOptions_716_;
v___y_692_ = v_a_674_;
goto v___jp_676_;
}
else
{
v___y_718_ = v___y_742_;
v___y_719_ = v___x_745_;
v___y_720_ = v___x_745_;
goto v___jp_717_;
}
}
else
{
v___y_718_ = v___y_742_;
v___y_719_ = v___x_745_;
v___y_720_ = v___x_746_;
goto v___jp_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___redArg___boxed(lean_object* v_declName_774_, lean_object* v_act_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_774_, v_act_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions(lean_object* v_00_u03b1_782_, lean_object* v_declName_783_, lean_object* v_act_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Meta_withEqnOptions___redArg(v_declName_783_, v_act_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object* v_00_u03b1_791_, lean_object* v_declName_792_, lean_object* v_act_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_withEqnOptions(v_00_u03b1_791_, v_declName_792_, v_act_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(lean_object* v_thm_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v_env_804_; lean_object* v_toConstantVal_805_; lean_object* v_value_806_; lean_object* v_all_807_; uint8_t v___y_809_; lean_object* v_type_817_; uint8_t v___x_818_; 
v___x_803_ = lean_st_ref_get(v___y_801_);
v_env_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc_ref_n(v_env_804_, 2);
lean_dec(v___x_803_);
v_toConstantVal_805_ = lean_ctor_get(v_thm_800_, 0);
v_value_806_ = lean_ctor_get(v_thm_800_, 1);
v_all_807_ = lean_ctor_get(v_thm_800_, 2);
v_type_817_ = lean_ctor_get(v_toConstantVal_805_, 2);
v___x_818_ = l_Lean_Environment_hasUnsafe(v_env_804_, v_type_817_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Environment_hasUnsafe(v_env_804_, v_value_806_);
v___y_809_ = v___x_819_;
goto v___jp_808_;
}
else
{
lean_dec_ref(v_env_804_);
v___y_809_ = v___x_818_;
goto v___jp_808_;
}
v___jp_808_:
{
if (v___y_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_810_, 0, v_thm_800_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_inc(v_all_807_);
lean_inc_ref(v_value_806_);
lean_inc_ref(v_toConstantVal_805_);
lean_dec_ref(v_thm_800_);
v___x_812_ = lean_box(0);
v___x_813_ = 0;
v___x_814_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_814_, 0, v_toConstantVal_805_);
lean_ctor_set(v___x_814_, 1, v_value_806_);
lean_ctor_set(v___x_814_, 2, v___x_812_);
lean_ctor_set(v___x_814_, 3, v_all_807_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*4, v___x_813_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(lean_object* v_thm_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_820_, v___y_821_);
lean_dec(v___y_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(lean_object* v_thm_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_824_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(lean_object* v_thm_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(lean_object* v_k_838_, lean_object* v_b_839_, lean_object* v_c_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
v___x_846_ = lean_apply_7(v_k_838_, v_b_839_, v_c_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, lean_box(0));
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(lean_object* v_k_847_, lean_object* v_b_848_, lean_object* v_c_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_847_, v_b_848_, v_c_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(lean_object* v_e_856_, lean_object* v_k_857_, uint8_t v_cleanupAnnotations_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___f_864_; uint8_t v___x_865_; uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___f_864_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_864_, 0, v_k_857_);
v___x_865_ = 1;
v___x_866_ = 0;
v___x_867_ = lean_box(0);
v___x_868_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_856_, v___x_865_, v___x_866_, v___x_865_, v___x_866_, v___x_867_, v___f_864_, v_cleanupAnnotations_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
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
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_868_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_868_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(lean_object* v_e_885_, lean_object* v_k_886_, lean_object* v_cleanupAnnotations_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_893_; lean_object* v_res_894_; 
v_cleanupAnnotations_boxed_893_ = lean_unbox(v_cleanupAnnotations_887_);
v_res_894_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_885_, v_k_886_, v_cleanupAnnotations_boxed_893_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(lean_object* v_00_u03b1_895_, lean_object* v_e_896_, lean_object* v_k_897_, uint8_t v_cleanupAnnotations_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_896_, v_k_897_, v_cleanupAnnotations_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(lean_object* v_00_u03b1_905_, lean_object* v_e_906_, lean_object* v_k_907_, lean_object* v_cleanupAnnotations_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_914_; lean_object* v_res_915_; 
v_cleanupAnnotations_boxed_914_ = lean_unbox(v_cleanupAnnotations_908_);
v_res_915_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_905_, v_e_906_, v_k_907_, v_cleanupAnnotations_boxed_914_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
if (lean_obj_tag(v_a_916_) == 0)
{
lean_object* v___x_918_; 
v___x_918_ = l_List_reverse___redArg(v_a_917_);
return v___x_918_;
}
else
{
lean_object* v_head_919_; lean_object* v_tail_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_929_; 
v_head_919_ = lean_ctor_get(v_a_916_, 0);
v_tail_920_ = lean_ctor_get(v_a_916_, 1);
v_isSharedCheck_929_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_929_ == 0)
{
v___x_922_ = v_a_916_;
v_isShared_923_ = v_isSharedCheck_929_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_tail_920_);
lean_inc(v_head_919_);
lean_dec(v_a_916_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_929_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = l_Lean_mkLevelParam(v_head_919_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v_a_917_);
lean_ctor_set(v___x_922_, 0, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_a_917_);
v___x_926_ = v_reuseFailAlloc_928_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
v_a_916_ = v_tail_920_;
v_a_917_ = v___x_926_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* v_toConstantVal_930_, lean_object* v_name_931_, lean_object* v_xs_932_, lean_object* v_body_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_name_939_; lean_object* v_levelParams_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_1010_; 
v_name_939_ = lean_ctor_get(v_toConstantVal_930_, 0);
v_levelParams_940_ = lean_ctor_get(v_toConstantVal_930_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_toConstantVal_930_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_toConstantVal_930_, 2);
lean_dec(v_unused_1011_);
v___x_942_ = v_toConstantVal_930_;
v_isShared_943_ = v_isSharedCheck_1010_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_levelParams_940_);
lean_inc(v_name_939_);
lean_dec(v_toConstantVal_930_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_1010_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_lhs_947_; lean_object* v___x_948_; 
v___x_944_ = lean_box(0);
lean_inc(v_levelParams_940_);
v___x_945_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_940_, v___x_944_);
v___x_946_ = l_Lean_mkConst(v_name_939_, v___x_945_);
v_lhs_947_ = l_Lean_mkAppN(v___x_946_, v_xs_932_);
lean_inc_ref(v_lhs_947_);
v___x_948_ = l_Lean_Meta_mkEq(v_lhs_947_, v_body_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; uint8_t v___x_950_; uint8_t v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = 0;
v___x_951_ = 1;
v___x_952_ = 1;
v___x_953_ = l_Lean_Meta_mkForallFVars(v_xs_932_, v_a_949_, v___x_950_, v___x_951_, v___x_951_, v___x_952_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = l_Lean_Meta_letToHave(v_a_954_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v___x_957_ = l_Lean_Meta_mkEqRefl(v_lhs_947_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = l_Lean_Meta_mkLambdaFVars(v_xs_932_, v_a_958_, v___x_950_, v___x_951_, v___x_950_, v___x_951_, v___x_952_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
lean_inc(v_name_931_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 2, v_a_956_);
lean_ctor_set(v___x_942_, 0, v_name_931_);
v___x_962_ = v___x_942_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_name_931_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_levelParams_940_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_a_956_);
v___x_962_ = v_reuseFailAlloc_969_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_967_; 
lean_inc(v_name_931_);
v___x_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_963_, 0, v_name_931_);
lean_ctor_set(v___x_963_, 1, v___x_944_);
v___x_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v_a_960_);
lean_ctor_set(v___x_964_, 2, v___x_963_);
v___x_965_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_964_, v___y_937_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref(v___x_965_);
v___x_967_ = l_Lean_addDecl(v_a_966_, v___x_950_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_968_; 
lean_dec_ref_known(v___x_967_, 1);
v___x_968_ = l_Lean_inferDefEqAttr(v_name_931_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_968_;
}
else
{
lean_dec(v_name_931_);
return v___x_967_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec(v_a_956_);
lean_del_object(v___x_942_);
lean_dec(v_levelParams_940_);
lean_dec(v_name_931_);
v_a_970_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_959_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_959_);
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
lean_dec(v_a_956_);
lean_del_object(v___x_942_);
lean_dec(v_levelParams_940_);
lean_dec(v_name_931_);
v_a_978_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_957_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_957_);
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
lean_dec_ref(v_lhs_947_);
lean_del_object(v___x_942_);
lean_dec(v_levelParams_940_);
lean_dec(v_name_931_);
v_a_986_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_955_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_955_);
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
lean_dec_ref(v_lhs_947_);
lean_del_object(v___x_942_);
lean_dec(v_levelParams_940_);
lean_dec(v_name_931_);
v_a_994_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_953_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_953_);
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
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_lhs_947_);
lean_del_object(v___x_942_);
lean_dec(v_levelParams_940_);
lean_dec(v_name_931_);
v_a_1002_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_948_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_948_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* v_toConstantVal_1012_, lean_object* v_name_1013_, lean_object* v_xs_1014_, lean_object* v_body_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(v_toConstantVal_1012_, v_name_1013_, v_xs_1014_, v_body_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec_ref(v_xs_1014_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* v_name_1022_, lean_object* v_info_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_toConstantVal_1029_; lean_object* v_value_1030_; lean_object* v___f_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; 
v_toConstantVal_1029_ = lean_ctor_get(v_info_1023_, 0);
lean_inc_ref(v_toConstantVal_1029_);
v_value_1030_ = lean_ctor_get(v_info_1023_, 1);
lean_inc_ref(v_value_1030_);
lean_dec_ref(v_info_1023_);
v___f_1031_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1031_, 0, v_toConstantVal_1029_);
lean_closure_set(v___f_1031_, 1, v_name_1022_);
v___x_1032_ = 1;
v___x_1033_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_1030_, v___f_1031_, v___x_1032_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(lean_object* v_name_1034_, lean_object* v_info_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(v_name_1034_, v_info_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm(lean_object* v_declName_1042_, lean_object* v_name_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1052_; lean_object* v_env_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_st_ref_get(v_a_1047_);
v_env_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc_ref(v_env_1053_);
lean_dec(v___x_1052_);
v___x_1054_ = 0;
lean_inc(v_declName_1042_);
v___x_1055_ = l_Lean_Environment_find_x3f(v_env_1053_, v_declName_1042_, v___x_1054_);
if (lean_obj_tag(v___x_1055_) == 1)
{
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1083_; 
v_val_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1083_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1083_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
if (lean_obj_tag(v_val_1056_) == 1)
{
lean_object* v_val_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_val_1060_ = lean_ctor_get(v_val_1056_, 0);
lean_inc_ref(v_val_1060_);
lean_dec_ref_known(v_val_1056_, 1);
lean_inc_n(v_name_1043_, 2);
v___x_1061_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed), 7, 2);
lean_closure_set(v___x_1061_, 0, v_name_1043_);
lean_closure_set(v___x_1061_, 1, v_val_1060_);
lean_inc(v_declName_1042_);
v___x_1062_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_1062_, 0, lean_box(0));
lean_closure_set(v___x_1062_, 1, v_declName_1042_);
lean_closure_set(v___x_1062_, 2, v___x_1061_);
v___x_1063_ = l_Lean_Meta_realizeConst(v_declName_1042_, v_name_1043_, v___x_1062_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1073_; 
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v___x_1063_, 0);
lean_dec(v_unused_1074_);
v___x_1065_ = v___x_1063_;
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
else
{
lean_dec(v___x_1063_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_name_1043_);
v___x_1068_ = v___x_1058_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_name_1043_);
v___x_1068_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1068_);
v___x_1070_ = v___x_1065_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_del_object(v___x_1058_);
lean_dec(v_name_1043_);
v_a_1075_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1063_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1063_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_del_object(v___x_1058_);
lean_dec(v_val_1056_);
lean_dec(v_name_1043_);
lean_dec(v_declName_1042_);
goto v___jp_1049_;
}
}
}
else
{
lean_dec(v___x_1055_);
lean_dec(v_name_1043_);
lean_dec(v_declName_1042_);
goto v___jp_1049_;
}
v___jp_1049_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpleEqThm___boxed(lean_object* v_declName_1084_, lean_object* v_name_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Meta_mkSimpleEqThm(v_declName_1084_, v_name_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1092_, lean_object* v_vals_1093_, lean_object* v_i_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_array_get_size(v_keys_1092_);
v___x_1097_ = lean_nat_dec_lt(v_i_1094_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec(v_i_1094_);
v___x_1098_ = lean_box(0);
return v___x_1098_;
}
else
{
lean_object* v_k_x27_1099_; uint8_t v___x_1100_; 
v_k_x27_1099_ = lean_array_fget_borrowed(v_keys_1092_, v_i_1094_);
v___x_1100_ = lean_name_eq(v_k_1095_, v_k_x27_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_unsigned_to_nat(1u);
v___x_1102_ = lean_nat_add(v_i_1094_, v___x_1101_);
lean_dec(v_i_1094_);
v_i_1094_ = v___x_1102_;
goto _start;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_array_fget_borrowed(v_vals_1093_, v_i_1094_);
lean_dec(v_i_1094_);
lean_inc(v___x_1104_);
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1106_, lean_object* v_vals_1107_, lean_object* v_i_1108_, lean_object* v_k_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1106_, v_vals_1107_, v_i_1108_, v_k_1109_);
lean_dec(v_k_1109_);
lean_dec_ref(v_vals_1107_);
lean_dec_ref(v_keys_1106_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_1111_, size_t v_x_1112_, lean_object* v_x_1113_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
lean_object* v_es_1114_; lean_object* v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; lean_object* v_j_1118_; lean_object* v___x_1119_; 
v_es_1114_ = lean_ctor_get(v_x_1111_, 0);
v___x_1115_ = lean_box(2);
v___x_1116_ = ((size_t)31ULL);
v___x_1117_ = lean_usize_land(v_x_1112_, v___x_1116_);
v_j_1118_ = lean_usize_to_nat(v___x_1117_);
v___x_1119_ = lean_array_get_borrowed(v___x_1115_, v_es_1114_, v_j_1118_);
lean_dec(v_j_1118_);
switch(lean_obj_tag(v___x_1119_))
{
case 0:
{
lean_object* v_key_1120_; lean_object* v_val_1121_; uint8_t v___x_1122_; 
v_key_1120_ = lean_ctor_get(v___x_1119_, 0);
v_val_1121_ = lean_ctor_get(v___x_1119_, 1);
v___x_1122_ = lean_name_eq(v_x_1113_, v_key_1120_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_box(0);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
lean_inc(v_val_1121_);
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_val_1121_);
return v___x_1124_;
}
}
case 1:
{
lean_object* v_node_1125_; size_t v___x_1126_; size_t v___x_1127_; 
v_node_1125_ = lean_ctor_get(v___x_1119_, 0);
v___x_1126_ = ((size_t)5ULL);
v___x_1127_ = lean_usize_shift_right(v_x_1112_, v___x_1126_);
v_x_1111_ = v_node_1125_;
v_x_1112_ = v___x_1127_;
goto _start;
}
default: 
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_box(0);
return v___x_1129_;
}
}
}
else
{
lean_object* v_ks_1130_; lean_object* v_vs_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_ks_1130_ = lean_ctor_get(v_x_1111_, 0);
v_vs_1131_ = lean_ctor_get(v_x_1111_, 1);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1130_, v_vs_1131_, v___x_1132_, v_x_1113_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
size_t v_x_340__boxed_1137_; lean_object* v_res_1138_; 
v_x_340__boxed_1137_ = lean_unbox_usize(v_x_1135_);
lean_dec(v_x_1135_);
v_res_1138_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1134_, v_x_340__boxed_1137_, v_x_1136_);
lean_dec(v_x_1136_);
lean_dec_ref(v_x_1134_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
uint64_t v___y_1142_; 
if (lean_obj_tag(v_x_1140_) == 0)
{
uint64_t v___x_1145_; 
v___x_1145_ = 1723ULL;
v___y_1142_ = v___x_1145_;
goto v___jp_1141_;
}
else
{
uint64_t v_hash_1146_; 
v_hash_1146_ = lean_ctor_get_uint64(v_x_1140_, sizeof(void*)*2);
v___y_1142_ = v_hash_1146_;
goto v___jp_1141_;
}
v___jp_1141_:
{
size_t v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_uint64_to_usize(v___y_1142_);
v___x_1144_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1139_, v___x_1143_, v_x_1140_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1147_, v_x_1148_);
lean_dec(v_x_1148_);
lean_dec_ref(v_x_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* v_thmName_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v_env_1154_; lean_object* v___x_1155_; lean_object* v_asyncMode_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1153_ = lean_st_ref_get(v_a_1151_);
v_env_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_ref(v_env_1154_);
lean_dec(v___x_1153_);
v___x_1155_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1156_ = lean_ctor_get(v___x_1155_, 2);
v___x_1157_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1158_ = lean_box(0);
v___x_1159_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1157_, v___x_1155_, v_env_1154_, v_asyncMode_1156_, v___x_1158_);
v___x_1160_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v___x_1159_, v_thmName_1150_);
lean_dec(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* v_thmName_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec(v_thmName_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* v_thmName_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_1166_, v_a_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* v_thmName_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_1171_, v_a_1172_, v_a_1173_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_thmName_1171_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(lean_object* v_00_u03b2_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(v_x_1177_, v_x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_1180_, lean_object* v_x_1181_, lean_object* v_x_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(v_00_u03b2_1180_, v_x_1181_, v_x_1182_);
lean_dec(v_x_1182_);
lean_dec_ref(v_x_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1184_, lean_object* v_x_1185_, size_t v_x_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_1185_, v_x_1186_, v_x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
size_t v_x_433__boxed_1193_; lean_object* v_res_1194_; 
v_x_433__boxed_1193_ = lean_unbox_usize(v_x_1191_);
lean_dec(v_x_1191_);
v_res_1194_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_1189_, v_x_1190_, v_x_433__boxed_1193_, v_x_1192_);
lean_dec(v_x_1192_);
lean_dec_ref(v_x_1190_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1195_, lean_object* v_keys_1196_, lean_object* v_vals_1197_, lean_object* v_heq_1198_, lean_object* v_i_1199_, lean_object* v_k_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1196_, v_vals_1197_, v_i_1199_, v_k_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1202_, lean_object* v_keys_1203_, lean_object* v_vals_1204_, lean_object* v_heq_1205_, lean_object* v_i_1206_, lean_object* v_k_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1202_, v_keys_1203_, v_vals_1204_, v_heq_1205_, v_i_1206_, v_k_1207_);
lean_dec(v_k_1207_);
lean_dec_ref(v_vals_1204_);
lean_dec_ref(v_keys_1203_);
return v_res_1208_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1209_, lean_object* v_i_1210_, lean_object* v_k_1211_){
_start:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_array_get_size(v_keys_1209_);
v___x_1213_ = lean_nat_dec_lt(v_i_1210_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v_i_1210_);
return v___x_1213_;
}
else
{
lean_object* v_k_x27_1214_; uint8_t v___x_1215_; 
v_k_x27_1214_ = lean_array_fget_borrowed(v_keys_1209_, v_i_1210_);
v___x_1215_ = lean_name_eq(v_k_1211_, v_k_x27_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = lean_nat_add(v_i_1210_, v___x_1216_);
lean_dec(v_i_1210_);
v_i_1210_ = v___x_1217_;
goto _start;
}
else
{
lean_dec(v_i_1210_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1219_, lean_object* v_i_1220_, lean_object* v_k_1221_){
_start:
{
uint8_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1219_, v_i_1220_, v_k_1221_);
lean_dec(v_k_1221_);
lean_dec_ref(v_keys_1219_);
v_r_1223_ = lean_box(v_res_1222_);
return v_r_1223_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(lean_object* v_x_1224_, size_t v_x_1225_, lean_object* v_x_1226_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 0)
{
lean_object* v_es_1227_; lean_object* v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; lean_object* v_j_1231_; lean_object* v___x_1232_; 
v_es_1227_ = lean_ctor_get(v_x_1224_, 0);
v___x_1228_ = lean_box(2);
v___x_1229_ = ((size_t)31ULL);
v___x_1230_ = lean_usize_land(v_x_1225_, v___x_1229_);
v_j_1231_ = lean_usize_to_nat(v___x_1230_);
v___x_1232_ = lean_array_get_borrowed(v___x_1228_, v_es_1227_, v_j_1231_);
lean_dec(v_j_1231_);
switch(lean_obj_tag(v___x_1232_))
{
case 0:
{
lean_object* v_key_1233_; uint8_t v___x_1234_; 
v_key_1233_ = lean_ctor_get(v___x_1232_, 0);
v___x_1234_ = lean_name_eq(v_x_1226_, v_key_1233_);
return v___x_1234_;
}
case 1:
{
lean_object* v_node_1235_; size_t v___x_1236_; size_t v___x_1237_; 
v_node_1235_ = lean_ctor_get(v___x_1232_, 0);
v___x_1236_ = ((size_t)5ULL);
v___x_1237_ = lean_usize_shift_right(v_x_1225_, v___x_1236_);
v_x_1224_ = v_node_1235_;
v_x_1225_ = v___x_1237_;
goto _start;
}
default: 
{
uint8_t v___x_1239_; 
v___x_1239_ = 0;
return v___x_1239_;
}
}
}
else
{
lean_object* v_ks_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_ks_1240_ = lean_ctor_get(v_x_1224_, 0);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_1240_, v___x_1241_, v_x_1226_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1243_, lean_object* v_x_1244_, lean_object* v_x_1245_){
_start:
{
size_t v_x_324__boxed_1246_; uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_x_324__boxed_1246_ = lean_unbox_usize(v_x_1244_);
lean_dec(v_x_1244_);
v_res_1247_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1243_, v_x_324__boxed_1246_, v_x_1245_);
lean_dec(v_x_1245_);
lean_dec_ref(v_x_1243_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
uint64_t v___y_1252_; 
if (lean_obj_tag(v_x_1250_) == 0)
{
uint64_t v___x_1255_; 
v___x_1255_ = 1723ULL;
v___y_1252_ = v___x_1255_;
goto v___jp_1251_;
}
else
{
uint64_t v_hash_1256_; 
v_hash_1256_ = lean_ctor_get_uint64(v_x_1250_, sizeof(void*)*2);
v___y_1252_ = v_hash_1256_;
goto v___jp_1251_;
}
v___jp_1251_:
{
size_t v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_uint64_to_usize(v___y_1252_);
v___x_1254_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1249_, v___x_1253_, v_x_1250_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1257_, v_x_1258_);
lean_dec(v_x_1258_);
lean_dec_ref(v_x_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* v_thmName_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v_env_1265_; lean_object* v___x_1266_; lean_object* v_asyncMode_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1264_ = lean_st_ref_get(v_a_1262_);
v_env_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc_ref(v_env_1265_);
lean_dec(v___x_1264_);
v___x_1266_ = l_Lean_Meta_eqnsExt;
v_asyncMode_1267_ = lean_ctor_get(v___x_1266_, 2);
v___x_1268_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
v___x_1269_ = lean_box(0);
v___x_1270_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1268_, v___x_1266_, v_env_1265_, v_asyncMode_1267_, v___x_1269_);
v___x_1271_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v___x_1270_, v_thmName_1261_);
lean_dec(v___x_1270_);
v___x_1272_ = lean_box(v___x_1271_);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* v_thmName_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec(v_thmName_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* v_thmName_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_1278_, v_a_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* v_thmName_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Meta_isEqnThm(v_thmName_1283_, v_a_1284_, v_a_1285_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_thmName_1283_);
return v_res_1287_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(lean_object* v_00_u03b2_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(v_x_1289_, v_x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(lean_object* v_00_u03b2_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_res_1295_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(v_00_u03b2_1292_, v_x_1293_, v_x_1294_);
lean_dec(v_x_1294_);
lean_dec_ref(v_x_1293_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(lean_object* v_00_u03b2_1297_, lean_object* v_x_1298_, size_t v_x_1299_, lean_object* v_x_1300_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_1298_, v_x_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
size_t v_x_413__boxed_1306_; uint8_t v_res_1307_; lean_object* v_r_1308_; 
v_x_413__boxed_1306_ = lean_unbox_usize(v_x_1304_);
lean_dec(v_x_1304_);
v_res_1307_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_1302_, v_x_1303_, v_x_413__boxed_1306_, v_x_1305_);
lean_dec(v_x_1305_);
lean_dec_ref(v_x_1303_);
v_r_1308_ = lean_box(v_res_1307_);
return v_r_1308_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1309_, lean_object* v_keys_1310_, lean_object* v_vals_1311_, lean_object* v_heq_1312_, lean_object* v_i_1313_, lean_object* v_k_1314_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_1310_, v_i_1313_, v_k_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1316_, lean_object* v_keys_1317_, lean_object* v_vals_1318_, lean_object* v_heq_1319_, lean_object* v_i_1320_, lean_object* v_k_1321_){
_start:
{
uint8_t v_res_1322_; lean_object* v_r_1323_; 
v_res_1322_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_1316_, v_keys_1317_, v_vals_1318_, v_heq_1319_, v_i_1320_, v_k_1321_);
lean_dec(v_k_1321_);
lean_dec_ref(v_vals_1318_);
lean_dec_ref(v_keys_1317_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
lean_object* v_ks_1328_; lean_object* v_vs_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1353_; 
v_ks_1328_ = lean_ctor_get(v_x_1324_, 0);
v_vs_1329_ = lean_ctor_get(v_x_1324_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_x_1324_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1331_ = v_x_1324_;
v_isShared_1332_ = v_isSharedCheck_1353_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_vs_1329_);
lean_inc(v_ks_1328_);
lean_dec(v_x_1324_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1353_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_array_get_size(v_ks_1328_);
v___x_1334_ = lean_nat_dec_lt(v_x_1325_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_dec(v_x_1325_);
v___x_1335_ = lean_array_push(v_ks_1328_, v_x_1326_);
v___x_1336_ = lean_array_push(v_vs_1329_, v_x_1327_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1336_);
lean_ctor_set(v___x_1331_, 0, v___x_1335_);
v___x_1338_ = v___x_1331_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
lean_object* v_k_x27_1340_; uint8_t v___x_1341_; 
v_k_x27_1340_ = lean_array_fget_borrowed(v_ks_1328_, v_x_1325_);
v___x_1341_ = lean_name_eq(v_x_1326_, v_k_x27_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1343_; 
if (v_isShared_1332_ == 0)
{
v___x_1343_ = v___x_1331_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_ks_1328_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_vs_1329_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_add(v_x_1325_, v___x_1344_);
lean_dec(v_x_1325_);
v_x_1324_ = v___x_1343_;
v_x_1325_ = v___x_1345_;
goto _start;
}
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = lean_array_fset(v_ks_1328_, v_x_1325_, v_x_1326_);
v___x_1349_ = lean_array_fset(v_vs_1329_, v_x_1325_, v_x_1327_);
lean_dec(v_x_1325_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1349_);
lean_ctor_set(v___x_1331_, 0, v___x_1348_);
v___x_1351_ = v___x_1331_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1354_, lean_object* v_k_1355_, lean_object* v_v_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1354_, v___x_1357_, v_k_1355_, v_v_1356_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(lean_object* v_x_1360_, size_t v_x_1361_, size_t v_x_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
if (lean_obj_tag(v_x_1360_) == 0)
{
lean_object* v_es_1365_; size_t v___x_1366_; size_t v___x_1367_; lean_object* v_j_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_es_1365_ = lean_ctor_get(v_x_1360_, 0);
v___x_1366_ = ((size_t)31ULL);
v___x_1367_ = lean_usize_land(v_x_1361_, v___x_1366_);
v_j_1368_ = lean_usize_to_nat(v___x_1367_);
v___x_1369_ = lean_array_get_size(v_es_1365_);
v___x_1370_ = lean_nat_dec_lt(v_j_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec(v_j_1368_);
lean_dec(v_x_1364_);
lean_dec(v_x_1363_);
return v_x_1360_;
}
else
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1409_; 
lean_inc_ref(v_es_1365_);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_x_1360_, 0);
lean_dec(v_unused_1410_);
v___x_1372_ = v_x_1360_;
v_isShared_1373_ = v_isSharedCheck_1409_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v_x_1360_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1409_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_v_1374_; lean_object* v___x_1375_; lean_object* v_xs_x27_1376_; lean_object* v___y_1378_; 
v_v_1374_ = lean_array_fget(v_es_1365_, v_j_1368_);
v___x_1375_ = lean_box(0);
v_xs_x27_1376_ = lean_array_fset(v_es_1365_, v_j_1368_, v___x_1375_);
switch(lean_obj_tag(v_v_1374_))
{
case 0:
{
lean_object* v_key_1383_; lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v_key_1383_ = lean_ctor_get(v_v_1374_, 0);
v_val_1384_ = lean_ctor_get(v_v_1374_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_v_1374_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1386_ = v_v_1374_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_inc(v_key_1383_);
lean_dec(v_v_1374_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_name_eq(v_x_1363_, v_key_1383_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_del_object(v___x_1386_);
v___x_1389_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1383_, v_val_1384_, v_x_1363_, v_x_1364_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
v___y_1378_ = v___x_1390_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1392_; 
lean_dec(v_val_1384_);
lean_dec(v_key_1383_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_x_1364_);
lean_ctor_set(v___x_1386_, 0, v_x_1363_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_x_1363_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_x_1364_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v___y_1378_ = v___x_1392_;
goto v___jp_1377_;
}
}
}
}
case 1:
{
lean_object* v_node_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1407_; 
v_node_1395_ = lean_ctor_get(v_v_1374_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_v_1374_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1397_ = v_v_1374_;
v_isShared_1398_ = v_isSharedCheck_1407_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_node_1395_);
lean_dec(v_v_1374_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1407_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1399_ = ((size_t)5ULL);
v___x_1400_ = lean_usize_shift_right(v_x_1361_, v___x_1399_);
v___x_1401_ = ((size_t)1ULL);
v___x_1402_ = lean_usize_add(v_x_1362_, v___x_1401_);
v___x_1403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_1395_, v___x_1400_, v___x_1402_, v_x_1363_, v_x_1364_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1403_);
v___x_1405_ = v___x_1397_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
v___y_1378_ = v___x_1405_;
goto v___jp_1377_;
}
}
}
default: 
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_x_1363_);
lean_ctor_set(v___x_1408_, 1, v_x_1364_);
v___y_1378_ = v___x_1408_;
goto v___jp_1377_;
}
}
v___jp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = lean_array_fset(v_xs_x27_1376_, v_j_1368_, v___y_1378_);
lean_dec(v_j_1368_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1379_);
v___x_1381_ = v___x_1372_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
else
{
lean_object* v_ks_1411_; lean_object* v_vs_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1430_; 
v_ks_1411_ = lean_ctor_get(v_x_1360_, 0);
v_vs_1412_ = lean_ctor_get(v_x_1360_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1414_ = v_x_1360_;
v_isShared_1415_ = v_isSharedCheck_1430_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_vs_1412_);
lean_inc(v_ks_1411_);
lean_dec(v_x_1360_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1430_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_ks_1411_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_vs_1412_);
v___x_1417_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v_newNode_1418_; size_t v___x_1419_; uint8_t v___x_1420_; 
v_newNode_1418_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_1417_, v_x_1363_, v_x_1364_);
v___x_1419_ = ((size_t)7ULL);
v___x_1420_ = lean_usize_dec_le(v___x_1419_, v_x_1362_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1418_);
v___x_1422_ = lean_unsigned_to_nat(4u);
v___x_1423_ = lean_nat_dec_lt(v___x_1421_, v___x_1422_);
lean_dec(v___x_1421_);
if (v___x_1423_ == 0)
{
lean_object* v_ks_1424_; lean_object* v_vs_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_ks_1424_ = lean_ctor_get(v_newNode_1418_, 0);
lean_inc_ref(v_ks_1424_);
v_vs_1425_ = lean_ctor_get(v_newNode_1418_, 1);
lean_inc_ref(v_vs_1425_);
lean_dec_ref(v_newNode_1418_);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
v___x_1428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_1362_, v_ks_1424_, v_vs_1425_, v___x_1426_, v___x_1427_);
lean_dec_ref(v_vs_1425_);
lean_dec_ref(v_ks_1424_);
return v___x_1428_;
}
else
{
return v_newNode_1418_;
}
}
else
{
return v_newNode_1418_;
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
v___x_1452_ = 1723ULL;
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
size_t v_x_625__boxed_1466_; size_t v_x_626__boxed_1467_; lean_object* v_res_1468_; 
v_x_625__boxed_1466_ = lean_unbox_usize(v_x_1462_);
lean_dec(v_x_1462_);
v_x_626__boxed_1467_ = lean_unbox_usize(v_x_1463_);
lean_dec(v_x_1463_);
v_res_1468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_1461_, v_x_625__boxed_1466_, v_x_626__boxed_1467_, v_x_1464_, v_x_1465_);
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
v___x_1477_ = 1723ULL;
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
v___x_1539_ = lean_st_ref_put(v_a_1517_, v___x_1538_);
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
size_t v_x_887__boxed_1580_; size_t v_x_888__boxed_1581_; lean_object* v_res_1582_; 
v_x_887__boxed_1580_ = lean_unbox_usize(v_x_1576_);
lean_dec(v_x_1576_);
v_x_888__boxed_1581_ = lean_unbox_usize(v_x_1577_);
lean_dec(v_x_1577_);
v_res_1582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_1574_, v_x_1575_, v_x_887__boxed_1580_, v_x_888__boxed_1581_, v_x_1578_, v_x_1579_);
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
v___x_2005_ = lean_st_ref_put(v___y_1966_, v___x_2004_);
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
lean_object* v_a_2036_; lean_object* v_defValue_2037_; uint8_t v___x_2038_; uint8_t v___y_2052_; uint8_t v___x_2053_; 
v_a_2036_ = lean_array_uget(v_as_2024_, v_i_2026_);
v_defValue_2037_ = lean_ctor_get(v_a_2036_, 1);
v___x_2038_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v___x_2023_, v_a_2036_);
v___x_2053_ = lean_unbox(v_defValue_2037_);
if (v___x_2053_ == 0)
{
if (v___x_2038_ == 0)
{
v___y_2052_ = v___x_2034_;
goto v___jp_2051_;
}
else
{
goto v___jp_2039_;
}
}
else
{
v___y_2052_ = v___x_2038_;
goto v___jp_2051_;
}
v___jp_2039_:
{
lean_object* v_name_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2049_; 
v_name_2040_ = lean_ctor_get(v_a_2036_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_a_2036_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v_a_2036_, 1);
lean_dec(v_unused_2050_);
v___x_2042_ = v_a_2036_;
v_isShared_2043_ = v_isSharedCheck_2049_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_name_2040_);
lean_dec(v_a_2036_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2049_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2044_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2044_, 0, v___x_2038_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v___x_2044_);
v___x_2046_ = v___x_2042_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_name_2040_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_array_push(v_b_2027_, v___x_2046_);
v_a_2030_ = v___x_2047_;
goto v___jp_2029_;
}
}
}
v___jp_2051_:
{
if (v___y_2052_ == 0)
{
goto v___jp_2039_;
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
v___x_2119_ = lean_st_ref_put(v___y_2101_, v___x_2118_);
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
v___x_2131_ = lean_st_ref_put(v___y_2100_, v___x_2130_);
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
v___x_2208_ = lean_st_ref_put(v___x_2205_, v___x_2207_);
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
v___x_2381_ = lean_st_ref_put(v___y_2359_, v___x_2380_);
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
v___x_2392_ = lean_st_ref_put(v___y_2362_, v___x_2391_);
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
lean_object* v___x_2417_; lean_object* v_env_2418_; lean_object* v___x_2419_; uint8_t v_isModule_2420_; 
v___x_2417_ = lean_st_ref_get(v___y_2415_);
v_env_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc_ref(v_env_2418_);
lean_dec(v___x_2417_);
v___x_2419_ = l_Lean_Environment_header(v_env_2418_);
v_isModule_2420_ = lean_ctor_get_uint8(v___x_2419_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2419_);
if (v_isModule_2420_ == 0)
{
lean_object* v___x_2421_; 
lean_dec_ref(v_env_2418_);
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
v___x_2421_ = lean_apply_5(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
return v___x_2421_;
}
else
{
uint8_t v_isExporting_2422_; 
v_isExporting_2422_ = lean_ctor_get_uint8(v_env_2418_, sizeof(void*)*8);
lean_dec_ref(v_env_2418_);
if (v_isExporting_2411_ == 0)
{
if (v_isExporting_2422_ == 0)
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
goto v___jp_2423_;
}
}
else
{
if (v_isExporting_2422_ == 0)
{
goto v___jp_2423_;
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
v___jp_2423_:
{
lean_object* v___x_2424_; lean_object* v_env_2425_; lean_object* v_nextMacroScope_2426_; lean_object* v_ngen_2427_; lean_object* v_auxDeclNGen_2428_; lean_object* v_traceState_2429_; lean_object* v_messages_2430_; lean_object* v_infoState_2431_; lean_object* v_snapshotTasks_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2486_; 
v___x_2424_ = lean_st_ref_take(v___y_2415_);
v_env_2425_ = lean_ctor_get(v___x_2424_, 0);
v_nextMacroScope_2426_ = lean_ctor_get(v___x_2424_, 1);
v_ngen_2427_ = lean_ctor_get(v___x_2424_, 2);
v_auxDeclNGen_2428_ = lean_ctor_get(v___x_2424_, 3);
v_traceState_2429_ = lean_ctor_get(v___x_2424_, 4);
v_messages_2430_ = lean_ctor_get(v___x_2424_, 6);
v_infoState_2431_ = lean_ctor_get(v___x_2424_, 7);
v_snapshotTasks_2432_ = lean_ctor_get(v___x_2424_, 8);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v___x_2424_, 5);
lean_dec(v_unused_2487_);
v___x_2434_ = v___x_2424_;
v_isShared_2435_ = v_isSharedCheck_2486_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_snapshotTasks_2432_);
lean_inc(v_infoState_2431_);
lean_inc(v_messages_2430_);
lean_inc(v_traceState_2429_);
lean_inc(v_auxDeclNGen_2428_);
lean_inc(v_ngen_2427_);
lean_inc(v_nextMacroScope_2426_);
lean_inc(v_env_2425_);
lean_dec(v___x_2424_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2486_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2436_ = l_Lean_Environment_setExporting(v_env_2425_, v_isExporting_2411_);
v___x_2437_ = lean_obj_once(&l_Lean_Meta_withEqnOptions___redArg___closed__2, &l_Lean_Meta_withEqnOptions___redArg___closed__2_once, _init_l_Lean_Meta_withEqnOptions___redArg___closed__2);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 5, v___x_2437_);
lean_ctor_set(v___x_2434_, 0, v___x_2436_);
v___x_2439_ = v___x_2434_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_nextMacroScope_2426_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_ngen_2427_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_auxDeclNGen_2428_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_traceState_2429_);
lean_ctor_set(v_reuseFailAlloc_2485_, 5, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2485_, 6, v_messages_2430_);
lean_ctor_set(v_reuseFailAlloc_2485_, 7, v_infoState_2431_);
lean_ctor_set(v_reuseFailAlloc_2485_, 8, v_snapshotTasks_2432_);
v___x_2439_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v_mctx_2442_; lean_object* v_zetaDeltaFVarIds_2443_; lean_object* v_postponed_2444_; lean_object* v_diag_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2483_; 
v___x_2440_ = lean_st_ref_put(v___y_2415_, v___x_2439_);
v___x_2441_ = lean_st_ref_take(v___y_2413_);
v_mctx_2442_ = lean_ctor_get(v___x_2441_, 0);
v_zetaDeltaFVarIds_2443_ = lean_ctor_get(v___x_2441_, 2);
v_postponed_2444_ = lean_ctor_get(v___x_2441_, 3);
v_diag_2445_ = lean_ctor_get(v___x_2441_, 4);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2441_, 1);
lean_dec(v_unused_2484_);
v___x_2447_ = v___x_2441_;
v_isShared_2448_ = v_isSharedCheck_2483_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_diag_2445_);
lean_inc(v_postponed_2444_);
lean_inc(v_zetaDeltaFVarIds_2443_);
lean_inc(v_mctx_2442_);
lean_dec(v___x_2441_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2483_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = lean_obj_once(&l_Lean_Meta_saveEqnAffectingOptions___closed__2, &l_Lean_Meta_saveEqnAffectingOptions___closed__2_once, _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v___x_2449_);
v___x_2451_ = v___x_2447_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_mctx_2442_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_zetaDeltaFVarIds_2443_);
lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_postponed_2444_);
lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_diag_2445_);
v___x_2451_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; lean_object* v_r_2453_; 
v___x_2452_ = lean_st_ref_put(v___y_2413_, v___x_2451_);
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
v_r_2453_ = lean_apply_5(v_x_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
if (lean_obj_tag(v_r_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2470_; 
v_a_2454_ = lean_ctor_get(v_r_2453_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_r_2453_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2456_ = v_r_2453_;
v_isShared_2457_ = v_isSharedCheck_2470_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v_r_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2470_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
lean_inc(v_a_2454_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set_tag(v___x_2456_, 1);
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
v___x_2460_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2415_, v_isExporting_2422_, v___x_2437_, v___y_2413_, v___x_2449_, v___x_2459_);
lean_dec_ref(v___x_2459_);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v___x_2460_, 0);
lean_dec(v_unused_2468_);
v___x_2462_ = v___x_2460_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_dec(v___x_2460_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v_a_2454_);
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2454_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
v_a_2471_ = lean_ctor_get(v_r_2453_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v_r_2453_, 1);
v___x_2472_ = lean_box(0);
v___x_2473_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_2415_, v_isExporting_2422_, v___x_2437_, v___y_2413_, v___x_2449_, v___x_2472_);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2473_, 0);
lean_dec(v_unused_2481_);
v___x_2475_ = v___x_2473_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_dec(v___x_2473_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set_tag(v___x_2475_, 1);
lean_ctor_set(v___x_2475_, 0, v_a_2471_);
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2471_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
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
v___x_2707_ = lean_st_ref_put(v___y_2680_, v___x_2706_);
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
v___x_2864_ = lean_st_ref_put(v___y_2808_, v___x_2863_);
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
v___x_2960_ = lean_st_ref_put(v___y_2897_, v___x_2959_);
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
v___x_3000_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_3000_, 10, v___x_2998_);
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
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1));
v___x_3010_ = l_Lean_Name_append(v___x_3009_, v___x_3008_);
return v___x_3010_;
}
}
static double _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3011_; double v___x_3012_; 
v___x_3011_ = lean_unsigned_to_nat(1000000000u);
v___x_3012_ = lean_float_of_nat(v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(lean_object* v___x_3013_, lean_object* v___f_3014_, lean_object* v_name_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_options_3019_; uint8_t v_hasTrace_3020_; 
v_options_3019_ = lean_ctor_get(v___y_3016_, 2);
v_hasTrace_3020_ = lean_ctor_get_uint8(v_options_3019_, sizeof(void*)*1);
if (v_hasTrace_3020_ == 0)
{
lean_object* v___x_3021_; lean_object* v_env_3022_; lean_object* v___x_3023_; 
lean_dec_ref(v___f_3014_);
v___x_3021_ = lean_st_ref_get(v___y_3017_);
v_env_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc_ref(v_env_3022_);
lean_dec(v___x_3021_);
lean_inc(v_name_3015_);
v___x_3023_ = l_Lean_Meta_declFromEqLikeName(v_env_3022_, v_name_3015_);
if (lean_obj_tag(v___x_3023_) == 1)
{
lean_object* v_val_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3129_; 
v_val_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3129_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_val_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3129_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_fst_3028_; lean_object* v_snd_3029_; lean_object* v___x_3030_; lean_object* v_env_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; 
v_fst_3028_ = lean_ctor_get(v_val_3024_, 0);
lean_inc_n(v_fst_3028_, 2);
v_snd_3029_ = lean_ctor_get(v_val_3024_, 1);
lean_inc_n(v_snd_3029_, 2);
lean_dec(v_val_3024_);
v___x_3030_ = lean_st_ref_get(v___y_3017_);
v_env_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc_ref(v_env_3031_);
lean_dec(v___x_3030_);
v___x_3032_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3031_, v_fst_3028_, v_snd_3029_);
v___x_3033_ = lean_name_eq(v_name_3015_, v___x_3032_);
lean_dec(v___x_3032_);
lean_dec(v_name_3015_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3036_; 
lean_dec(v_snd_3029_);
lean_dec(v_fst_3028_);
lean_dec(v___x_3013_);
v___x_3034_ = lean_box(v_hasTrace_3020_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set_tag(v___x_3026_, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3034_);
v___x_3036_ = v___x_3026_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
else
{
uint8_t v___x_3038_; lean_object* v_a_3040_; 
lean_inc(v_snd_3029_);
v___x_3038_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3029_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3054_; uint8_t v___x_3055_; lean_object* v_a_3057_; 
lean_del_object(v___x_3026_);
v___x_3054_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3055_ = lean_string_dec_eq(v_snd_3029_, v___x_3054_);
lean_dec(v_snd_3029_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec(v_fst_3028_);
lean_dec(v___x_3013_);
v___x_3069_ = lean_box(v_hasTrace_3020_);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
return v___x_3070_;
}
else
{
uint8_t v___x_3071_; uint8_t v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; uint64_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3071_ = 1;
v___x_3072_ = 0;
v___x_3073_ = 2;
v___x_3074_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3074_, 0, v___x_3038_);
lean_ctor_set_uint8(v___x_3074_, 1, v___x_3038_);
lean_ctor_set_uint8(v___x_3074_, 2, v___x_3038_);
lean_ctor_set_uint8(v___x_3074_, 3, v___x_3038_);
lean_ctor_set_uint8(v___x_3074_, 4, v___x_3038_);
lean_ctor_set_uint8(v___x_3074_, 5, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 6, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 7, v___x_3038_);
lean_ctor_set_uint8(v___x_3074_, 8, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 9, v___x_3071_);
lean_ctor_set_uint8(v___x_3074_, 10, v___x_3072_);
lean_ctor_set_uint8(v___x_3074_, 11, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 12, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 13, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 14, v___x_3073_);
lean_ctor_set_uint8(v___x_3074_, 15, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 16, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 17, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 18, v___x_3055_);
lean_ctor_set_uint8(v___x_3074_, 19, v___x_3038_);
v___x_3075_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3074_);
v___x_3076_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set_uint64(v___x_3076_, sizeof(void*)*1, v___x_3075_);
v___x_3077_ = lean_unsigned_to_nat(0u);
v___x_3078_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3079_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3080_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3081_ = lean_box(0);
lean_inc(v___x_3013_);
v___x_3082_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3082_, 0, v___x_3076_);
lean_ctor_set(v___x_3082_, 1, v___x_3013_);
lean_ctor_set(v___x_3082_, 2, v___x_3079_);
lean_ctor_set(v___x_3082_, 3, v___x_3080_);
lean_ctor_set(v___x_3082_, 4, v___x_3081_);
lean_ctor_set(v___x_3082_, 5, v___x_3077_);
lean_ctor_set(v___x_3082_, 6, v___x_3081_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*7, v___x_3038_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*7 + 1, v___x_3038_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*7 + 2, v___x_3038_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*7 + 3, v___x_3033_);
v___x_3083_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3084_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3085_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3083_);
lean_ctor_set(v___x_3086_, 1, v___x_3084_);
lean_ctor_set(v___x_3086_, 2, v___x_3013_);
lean_ctor_set(v___x_3086_, 3, v___x_3078_);
lean_ctor_set(v___x_3086_, 4, v___x_3085_);
v___x_3087_ = lean_st_mk_ref(v___x_3086_);
v___x_3088_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3028_, v___x_3033_, v___x_3082_, v___x_3087_, v___y_3016_, v___y_3017_);
lean_dec_ref_known(v___x_3082_, 7);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3090_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3090_ = lean_st_ref_get(v___x_3087_);
lean_dec(v___x_3087_);
lean_dec(v___x_3090_);
v_a_3057_ = v_a_3089_;
goto v___jp_3056_;
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
v_a_3057_ = v_a_3091_;
goto v___jp_3056_;
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
v___jp_3056_:
{
if (lean_obj_tag(v_a_3057_) == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_box(v___x_3038_);
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
return v___x_3059_;
}
else
{
lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3067_; 
v_isSharedCheck_3067_ = !lean_is_exclusive(v_a_3057_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; 
v_unused_3068_ = lean_ctor_get(v_a_3057_, 0);
lean_dec(v_unused_3068_);
v___x_3061_ = v_a_3057_;
v_isShared_3062_ = v_isSharedCheck_3067_;
goto v_resetjp_3060_;
}
else
{
lean_dec(v_a_3057_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3067_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_box(v___x_3055_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3063_);
v___x_3065_ = v___x_3061_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
uint8_t v___x_3100_; uint8_t v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; uint64_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec(v_snd_3029_);
v___x_3100_ = 1;
v___x_3101_ = 0;
v___x_3102_ = 2;
v___x_3103_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3103_, 0, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3103_, 1, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3103_, 2, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3103_, 3, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3103_, 4, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3103_, 5, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 6, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 7, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3103_, 8, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 9, v___x_3100_);
lean_ctor_set_uint8(v___x_3103_, 10, v___x_3101_);
lean_ctor_set_uint8(v___x_3103_, 11, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 12, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 13, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 14, v___x_3102_);
lean_ctor_set_uint8(v___x_3103_, 15, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 16, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 17, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 18, v___x_3038_);
lean_ctor_set_uint8(v___x_3103_, 19, v_hasTrace_3020_);
v___x_3104_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3103_);
v___x_3105_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set_uint64(v___x_3105_, sizeof(void*)*1, v___x_3104_);
v___x_3106_ = lean_unsigned_to_nat(0u);
v___x_3107_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3108_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3109_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3110_ = lean_box(0);
lean_inc(v___x_3013_);
v___x_3111_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3111_, 0, v___x_3105_);
lean_ctor_set(v___x_3111_, 1, v___x_3013_);
lean_ctor_set(v___x_3111_, 2, v___x_3108_);
lean_ctor_set(v___x_3111_, 3, v___x_3109_);
lean_ctor_set(v___x_3111_, 4, v___x_3110_);
lean_ctor_set(v___x_3111_, 5, v___x_3106_);
lean_ctor_set(v___x_3111_, 6, v___x_3110_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 1, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 2, v_hasTrace_3020_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*7 + 3, v___x_3033_);
v___x_3112_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3113_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3114_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3112_);
lean_ctor_set(v___x_3115_, 1, v___x_3113_);
lean_ctor_set(v___x_3115_, 2, v___x_3013_);
lean_ctor_set(v___x_3115_, 3, v___x_3107_);
lean_ctor_set(v___x_3115_, 4, v___x_3114_);
v___x_3116_ = lean_st_mk_ref(v___x_3115_);
v___x_3117_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3028_, v___x_3111_, v___x_3116_, v___y_3016_, v___y_3017_);
lean_dec_ref_known(v___x_3111_, 7);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = lean_st_ref_get(v___x_3116_);
lean_dec(v___x_3116_);
lean_dec(v___x_3119_);
v_a_3040_ = v_a_3118_;
goto v___jp_3039_;
}
else
{
lean_dec(v___x_3116_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3120_; 
v_a_3120_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3117_, 1);
v_a_3040_ = v_a_3120_;
goto v___jp_3039_;
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_del_object(v___x_3026_);
v_a_3121_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3117_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3117_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
v___jp_3039_:
{
if (lean_obj_tag(v_a_3040_) == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3041_ = lean_box(v_hasTrace_3020_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set_tag(v___x_3026_, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3041_);
v___x_3043_ = v___x_3026_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3052_; 
lean_del_object(v___x_3026_);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_a_3040_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v_a_3040_, 0);
lean_dec(v_unused_3053_);
v___x_3046_ = v_a_3040_;
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
else
{
lean_dec(v_a_3040_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = lean_box(v___x_3038_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec(v___x_3023_);
lean_dec(v_name_3015_);
lean_dec(v___x_3013_);
v___x_3130_ = lean_box(v_hasTrace_3020_);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3132_; lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v_a_3141_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v_a_3156_; lean_object* v___y_3159_; lean_object* v___y_3160_; uint8_t v_a_3161_; uint8_t v___y_3165_; uint8_t v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v_a_3169_; uint8_t v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; uint8_t v___y_3174_; lean_object* v_a_3175_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v_a_3179_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v_a_3191_; uint8_t v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3198_; lean_object* v_a_3199_; lean_object* v___y_3201_; lean_object* v___y_3202_; uint8_t v___y_3203_; lean_object* v_a_3204_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v_a_3209_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; 
v_inheritedTraceOptions_3132_ = lean_ctor_get(v___y_3016_, 13);
lean_inc(v_name_3015_);
v___f_3133_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3133_, 0, v_name_3015_);
v___x_3134_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3135_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1));
v___x_3136_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3137_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3132_, v_options_3019_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3346_ = l_Lean_trace_profiler;
v___x_3347_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3019_, v___x_3346_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; lean_object* v_env_3349_; lean_object* v___x_3350_; 
lean_dec_ref(v___f_3133_);
lean_dec_ref(v___f_3014_);
v___x_3348_ = lean_st_ref_get(v___y_3017_);
v_env_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc_ref(v_env_3349_);
lean_dec(v___x_3348_);
lean_inc(v_name_3015_);
v___x_3350_ = l_Lean_Meta_declFromEqLikeName(v_env_3349_, v_name_3015_);
if (lean_obj_tag(v___x_3350_) == 1)
{
lean_object* v_val_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3456_; 
v_val_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3456_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_val_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3456_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v_fst_3355_; lean_object* v_snd_3356_; lean_object* v___x_3357_; lean_object* v_env_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_fst_3355_ = lean_ctor_get(v_val_3351_, 0);
lean_inc_n(v_fst_3355_, 2);
v_snd_3356_ = lean_ctor_get(v_val_3351_, 1);
lean_inc_n(v_snd_3356_, 2);
lean_dec(v_val_3351_);
v___x_3357_ = lean_st_ref_get(v___y_3017_);
v_env_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc_ref(v_env_3358_);
lean_dec(v___x_3357_);
v___x_3359_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3358_, v_fst_3355_, v_snd_3356_);
v___x_3360_ = lean_name_eq(v_name_3015_, v___x_3359_);
lean_dec(v___x_3359_);
lean_dec(v_name_3015_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
lean_dec(v_snd_3356_);
lean_dec(v_fst_3355_);
lean_dec(v___x_3013_);
v___x_3361_ = lean_box(v___x_3347_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set_tag(v___x_3353_, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3361_);
v___x_3363_ = v___x_3353_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
else
{
uint8_t v___x_3365_; lean_object* v_a_3367_; 
lean_inc(v_snd_3356_);
v___x_3365_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3356_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v_a_3384_; 
lean_del_object(v___x_3353_);
v___x_3381_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3382_ = lean_string_dec_eq(v_snd_3356_, v___x_3381_);
lean_dec(v_snd_3356_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_dec(v_fst_3355_);
lean_dec(v___x_3013_);
v___x_3396_ = lean_box(v___x_3347_);
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
return v___x_3397_;
}
else
{
uint8_t v___x_3398_; uint8_t v___x_3399_; uint8_t v___x_3400_; lean_object* v___x_3401_; uint64_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3398_ = 1;
v___x_3399_ = 0;
v___x_3400_ = 2;
v___x_3401_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3401_, 0, v___x_3365_);
lean_ctor_set_uint8(v___x_3401_, 1, v___x_3365_);
lean_ctor_set_uint8(v___x_3401_, 2, v___x_3365_);
lean_ctor_set_uint8(v___x_3401_, 3, v___x_3365_);
lean_ctor_set_uint8(v___x_3401_, 4, v___x_3365_);
lean_ctor_set_uint8(v___x_3401_, 5, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 6, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 7, v___x_3365_);
lean_ctor_set_uint8(v___x_3401_, 8, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 9, v___x_3398_);
lean_ctor_set_uint8(v___x_3401_, 10, v___x_3399_);
lean_ctor_set_uint8(v___x_3401_, 11, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 12, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 13, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 14, v___x_3400_);
lean_ctor_set_uint8(v___x_3401_, 15, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 16, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 17, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 18, v___x_3382_);
lean_ctor_set_uint8(v___x_3401_, 19, v___x_3365_);
v___x_3402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3401_);
v___x_3403_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set_uint64(v___x_3403_, sizeof(void*)*1, v___x_3402_);
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3408_ = lean_box(0);
lean_inc(v___x_3013_);
v___x_3409_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3409_, 0, v___x_3403_);
lean_ctor_set(v___x_3409_, 1, v___x_3013_);
lean_ctor_set(v___x_3409_, 2, v___x_3406_);
lean_ctor_set(v___x_3409_, 3, v___x_3407_);
lean_ctor_set(v___x_3409_, 4, v___x_3408_);
lean_ctor_set(v___x_3409_, 5, v___x_3404_);
lean_ctor_set(v___x_3409_, 6, v___x_3408_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*7, v___x_3365_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*7 + 1, v___x_3365_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*7 + 2, v___x_3365_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*7 + 3, v_hasTrace_3020_);
v___x_3410_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3411_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3412_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3410_);
lean_ctor_set(v___x_3413_, 1, v___x_3411_);
lean_ctor_set(v___x_3413_, 2, v___x_3013_);
lean_ctor_set(v___x_3413_, 3, v___x_3405_);
lean_ctor_set(v___x_3413_, 4, v___x_3412_);
v___x_3414_ = lean_st_mk_ref(v___x_3413_);
v___x_3415_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3355_, v_hasTrace_3020_, v___x_3409_, v___x_3414_, v___y_3016_, v___y_3017_);
lean_dec_ref_known(v___x_3409_, 7);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
v___x_3417_ = lean_st_ref_get(v___x_3414_);
lean_dec(v___x_3414_);
lean_dec(v___x_3417_);
v_a_3384_ = v_a_3416_;
goto v___jp_3383_;
}
else
{
lean_dec(v___x_3414_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3418_; 
v_a_3418_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3415_, 1);
v_a_3384_ = v_a_3418_;
goto v___jp_3383_;
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
v_a_3419_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3415_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3415_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
v___jp_3383_:
{
if (lean_obj_tag(v_a_3384_) == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = lean_box(v___x_3365_);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
return v___x_3386_;
}
else
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3394_; 
v_isSharedCheck_3394_ = !lean_is_exclusive(v_a_3384_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v_a_3384_, 0);
lean_dec(v_unused_3395_);
v___x_3388_ = v_a_3384_;
v_isShared_3389_ = v_isSharedCheck_3394_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v_a_3384_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3394_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_box(v___x_3382_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3390_);
v___x_3392_ = v___x_3388_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
else
{
uint8_t v___x_3427_; uint8_t v___x_3428_; uint8_t v___x_3429_; lean_object* v___x_3430_; uint64_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec(v_snd_3356_);
v___x_3427_ = 1;
v___x_3428_ = 0;
v___x_3429_ = 2;
v___x_3430_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3430_, 0, v___x_3347_);
lean_ctor_set_uint8(v___x_3430_, 1, v___x_3347_);
lean_ctor_set_uint8(v___x_3430_, 2, v___x_3347_);
lean_ctor_set_uint8(v___x_3430_, 3, v___x_3347_);
lean_ctor_set_uint8(v___x_3430_, 4, v___x_3347_);
lean_ctor_set_uint8(v___x_3430_, 5, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 6, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 7, v___x_3347_);
lean_ctor_set_uint8(v___x_3430_, 8, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 9, v___x_3427_);
lean_ctor_set_uint8(v___x_3430_, 10, v___x_3428_);
lean_ctor_set_uint8(v___x_3430_, 11, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 12, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 13, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 14, v___x_3429_);
lean_ctor_set_uint8(v___x_3430_, 15, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 16, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 17, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 18, v___x_3365_);
lean_ctor_set_uint8(v___x_3430_, 19, v___x_3347_);
v___x_3431_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3432_, 0, v___x_3430_);
lean_ctor_set_uint64(v___x_3432_, sizeof(void*)*1, v___x_3431_);
v___x_3433_ = lean_unsigned_to_nat(0u);
v___x_3434_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3436_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3437_ = lean_box(0);
lean_inc(v___x_3013_);
v___x_3438_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3438_, 0, v___x_3432_);
lean_ctor_set(v___x_3438_, 1, v___x_3013_);
lean_ctor_set(v___x_3438_, 2, v___x_3435_);
lean_ctor_set(v___x_3438_, 3, v___x_3436_);
lean_ctor_set(v___x_3438_, 4, v___x_3437_);
lean_ctor_set(v___x_3438_, 5, v___x_3433_);
lean_ctor_set(v___x_3438_, 6, v___x_3437_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*7, v___x_3347_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*7 + 1, v___x_3347_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*7 + 2, v___x_3347_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*7 + 3, v_hasTrace_3020_);
v___x_3439_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3440_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3441_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3439_);
lean_ctor_set(v___x_3442_, 1, v___x_3440_);
lean_ctor_set(v___x_3442_, 2, v___x_3013_);
lean_ctor_set(v___x_3442_, 3, v___x_3434_);
lean_ctor_set(v___x_3442_, 4, v___x_3441_);
v___x_3443_ = lean_st_mk_ref(v___x_3442_);
v___x_3444_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3355_, v___x_3438_, v___x_3443_, v___y_3016_, v___y_3017_);
lean_dec_ref_known(v___x_3438_, 7);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
v___x_3446_ = lean_st_ref_get(v___x_3443_);
lean_dec(v___x_3443_);
lean_dec(v___x_3446_);
v_a_3367_ = v_a_3445_;
goto v___jp_3366_;
}
else
{
lean_dec(v___x_3443_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3447_; 
v_a_3447_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3444_, 1);
v_a_3367_ = v_a_3447_;
goto v___jp_3366_;
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_del_object(v___x_3353_);
v_a_3448_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3444_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3444_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
v___jp_3366_:
{
if (lean_obj_tag(v_a_3367_) == 0)
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = lean_box(v___x_3347_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set_tag(v___x_3353_, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3368_);
v___x_3370_ = v___x_3353_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
else
{
lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3379_; 
lean_del_object(v___x_3353_);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_a_3367_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; 
v_unused_3380_ = lean_ctor_get(v_a_3367_, 0);
lean_dec(v_unused_3380_);
v___x_3373_ = v_a_3367_;
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
else
{
lean_dec(v_a_3367_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_box(v___x_3365_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set_tag(v___x_3373_, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3375_);
v___x_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_dec(v___x_3350_);
lean_dec(v_name_3015_);
lean_dec(v___x_3013_);
v___x_3457_ = lean_box(v___x_3347_);
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
}
else
{
goto v___jp_3218_;
}
}
else
{
goto v___jp_3218_;
}
v___jp_3138_:
{
lean_object* v___x_3142_; double v___x_3143_; double v___x_3144_; double v___x_3145_; double v___x_3146_; double v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3142_ = lean_io_mono_nanos_now();
v___x_3143_ = lean_float_of_nat(v___y_3140_);
v___x_3144_ = lean_float_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3145_ = lean_float_div(v___x_3143_, v___x_3144_);
v___x_3146_ = lean_float_of_nat(v___x_3142_);
v___x_3147_ = lean_float_div(v___x_3146_, v___x_3144_);
v___x_3148_ = lean_box_float(v___x_3145_);
v___x_3149_ = lean_box_float(v___x_3147_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v_a_3141_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3134_, v_hasTrace_3020_, v___x_3135_, v_options_3019_, v___x_3137_, v___y_3139_, v___f_3133_, v___x_3151_, v___y_3016_, v___y_3017_);
return v___x_3152_;
}
v___jp_3153_:
{
lean_object* v___x_3157_; 
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v_a_3156_);
v___y_3139_ = v___y_3155_;
v___y_3140_ = v___y_3154_;
v_a_3141_ = v___x_3157_;
goto v___jp_3138_;
}
v___jp_3158_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_box(v_a_3161_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
v___y_3139_ = v___y_3160_;
v___y_3140_ = v___y_3159_;
v_a_3141_ = v___x_3163_;
goto v___jp_3138_;
}
v___jp_3164_:
{
if (lean_obj_tag(v_a_3169_) == 0)
{
v___y_3159_ = v___y_3168_;
v___y_3160_ = v___y_3167_;
v_a_3161_ = v___y_3166_;
goto v___jp_3158_;
}
else
{
lean_dec_ref_known(v_a_3169_, 1);
v___y_3159_ = v___y_3168_;
v___y_3160_ = v___y_3167_;
v_a_3161_ = v___y_3165_;
goto v___jp_3158_;
}
}
v___jp_3170_:
{
if (lean_obj_tag(v_a_3175_) == 0)
{
v___y_3159_ = v___y_3173_;
v___y_3160_ = v___y_3172_;
v_a_3161_ = v___y_3171_;
goto v___jp_3158_;
}
else
{
lean_dec_ref_known(v_a_3175_, 1);
v___y_3159_ = v___y_3173_;
v___y_3160_ = v___y_3172_;
v_a_3161_ = v___y_3174_;
goto v___jp_3158_;
}
}
v___jp_3176_:
{
lean_object* v___x_3180_; double v___x_3181_; double v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3180_ = lean_io_get_num_heartbeats();
v___x_3181_ = lean_float_of_nat(v___y_3178_);
v___x_3182_ = lean_float_of_nat(v___x_3180_);
v___x_3183_ = lean_box_float(v___x_3181_);
v___x_3184_ = lean_box_float(v___x_3182_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v_a_3179_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_3134_, v_hasTrace_3020_, v___x_3135_, v_options_3019_, v___x_3137_, v___y_3177_, v___f_3133_, v___x_3186_, v___y_3016_, v___y_3017_);
return v___x_3187_;
}
v___jp_3188_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = lean_box(v_a_3191_);
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
v___y_3177_ = v___y_3189_;
v___y_3178_ = v___y_3190_;
v_a_3179_ = v___x_3193_;
goto v___jp_3176_;
}
v___jp_3194_:
{
if (lean_obj_tag(v_a_3199_) == 0)
{
v___y_3189_ = v___y_3196_;
v___y_3190_ = v___y_3197_;
v_a_3191_ = v___y_3198_;
goto v___jp_3188_;
}
else
{
lean_dec_ref_known(v_a_3199_, 1);
v___y_3189_ = v___y_3196_;
v___y_3190_ = v___y_3197_;
v_a_3191_ = v___y_3195_;
goto v___jp_3188_;
}
}
v___jp_3200_:
{
if (lean_obj_tag(v_a_3204_) == 0)
{
uint8_t v___x_3205_; 
v___x_3205_ = 0;
v___y_3189_ = v___y_3201_;
v___y_3190_ = v___y_3202_;
v_a_3191_ = v___x_3205_;
goto v___jp_3188_;
}
else
{
lean_dec_ref_known(v_a_3204_, 1);
v___y_3189_ = v___y_3201_;
v___y_3190_ = v___y_3202_;
v_a_3191_ = v___y_3203_;
goto v___jp_3188_;
}
}
v___jp_3206_:
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_a_3209_);
v___y_3177_ = v___y_3207_;
v___y_3178_ = v___y_3208_;
v_a_3179_ = v___x_3210_;
goto v___jp_3176_;
}
v___jp_3211_:
{
if (lean_obj_tag(v___y_3214_) == 0)
{
lean_object* v_a_3215_; uint8_t v___x_3216_; 
v_a_3215_ = lean_ctor_get(v___y_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___y_3214_, 1);
v___x_3216_ = lean_unbox(v_a_3215_);
lean_dec(v_a_3215_);
v___y_3189_ = v___y_3212_;
v___y_3190_ = v___y_3213_;
v_a_3191_ = v___x_3216_;
goto v___jp_3188_;
}
else
{
lean_object* v_a_3217_; 
v_a_3217_ = lean_ctor_get(v___y_3214_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v___y_3214_, 1);
v___y_3207_ = v___y_3212_;
v___y_3208_ = v___y_3213_;
v_a_3209_ = v_a_3217_;
goto v___jp_3206_;
}
}
v___jp_3218_:
{
lean_object* v___x_3219_; lean_object* v_a_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3219_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_3017_);
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref(v___x_3219_);
v___x_3221_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3222_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_options_3019_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v_env_3225_; lean_object* v___x_3226_; 
lean_dec_ref(v___f_3014_);
v___x_3223_ = lean_io_mono_nanos_now();
v___x_3224_ = lean_st_ref_get(v___y_3017_);
v_env_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_env_3225_);
lean_dec(v___x_3224_);
lean_inc(v_name_3015_);
v___x_3226_ = l_Lean_Meta_declFromEqLikeName(v_env_3225_, v_name_3015_);
if (lean_obj_tag(v___x_3226_) == 1)
{
lean_object* v_val_3227_; lean_object* v_fst_3228_; lean_object* v_snd_3229_; lean_object* v___x_3230_; lean_object* v_env_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v_val_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_val_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v_fst_3228_ = lean_ctor_get(v_val_3227_, 0);
lean_inc_n(v_fst_3228_, 2);
v_snd_3229_ = lean_ctor_get(v_val_3227_, 1);
lean_inc_n(v_snd_3229_, 2);
lean_dec(v_val_3227_);
v___x_3230_ = lean_st_ref_get(v___y_3017_);
v_env_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc_ref(v_env_3231_);
lean_dec(v___x_3230_);
v___x_3232_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3231_, v_fst_3228_, v_snd_3229_);
v___x_3233_ = lean_name_eq(v_name_3015_, v___x_3232_);
lean_dec(v___x_3232_);
lean_dec(v_name_3015_);
if (v___x_3233_ == 0)
{
lean_dec(v_snd_3229_);
lean_dec(v_fst_3228_);
lean_dec(v___x_3013_);
v___y_3159_ = v___x_3223_;
v___y_3160_ = v_a_3220_;
v_a_3161_ = v___x_3222_;
goto v___jp_3158_;
}
else
{
uint8_t v___x_3234_; 
lean_inc(v_snd_3229_);
v___x_3234_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3229_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3236_ = lean_string_dec_eq(v_snd_3229_, v___x_3235_);
lean_dec(v_snd_3229_);
if (v___x_3236_ == 0)
{
lean_dec(v_fst_3228_);
lean_dec(v___x_3013_);
v___y_3159_ = v___x_3223_;
v___y_3160_ = v_a_3220_;
v_a_3161_ = v___x_3222_;
goto v___jp_3158_;
}
else
{
uint8_t v___x_3237_; uint8_t v___x_3238_; uint8_t v___x_3239_; lean_object* v___x_3240_; uint64_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3237_ = 1;
v___x_3238_ = 0;
v___x_3239_ = 2;
v___x_3240_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3240_, 0, v___x_3234_);
lean_ctor_set_uint8(v___x_3240_, 1, v___x_3234_);
lean_ctor_set_uint8(v___x_3240_, 2, v___x_3234_);
lean_ctor_set_uint8(v___x_3240_, 3, v___x_3234_);
lean_ctor_set_uint8(v___x_3240_, 4, v___x_3234_);
lean_ctor_set_uint8(v___x_3240_, 5, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 6, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 7, v___x_3234_);
lean_ctor_set_uint8(v___x_3240_, 8, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 9, v___x_3237_);
lean_ctor_set_uint8(v___x_3240_, 10, v___x_3238_);
lean_ctor_set_uint8(v___x_3240_, 11, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 12, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 13, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 14, v___x_3239_);
lean_ctor_set_uint8(v___x_3240_, 15, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 16, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 17, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 18, v___x_3236_);
lean_ctor_set_uint8(v___x_3240_, 19, v___x_3234_);
v___x_3241_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set_uint64(v___x_3242_, sizeof(void*)*1, v___x_3241_);
v___x_3243_ = lean_unsigned_to_nat(0u);
v___x_3244_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3245_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3246_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3247_ = lean_box(0);
lean_inc(v___x_3013_);
v___x_3248_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3248_, 0, v___x_3242_);
lean_ctor_set(v___x_3248_, 1, v___x_3013_);
lean_ctor_set(v___x_3248_, 2, v___x_3245_);
lean_ctor_set(v___x_3248_, 3, v___x_3246_);
lean_ctor_set(v___x_3248_, 4, v___x_3247_);
lean_ctor_set(v___x_3248_, 5, v___x_3243_);
lean_ctor_set(v___x_3248_, 6, v___x_3247_);
lean_ctor_set_uint8(v___x_3248_, sizeof(void*)*7, v___x_3234_);
lean_ctor_set_uint8(v___x_3248_, sizeof(void*)*7 + 1, v___x_3234_);
lean_ctor_set_uint8(v___x_3248_, sizeof(void*)*7 + 2, v___x_3234_);
lean_ctor_set_uint8(v___x_3248_, sizeof(void*)*7 + 3, v_hasTrace_3020_);
v___x_3249_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3250_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3251_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3249_);
lean_ctor_set(v___x_3252_, 1, v___x_3250_);
lean_ctor_set(v___x_3252_, 2, v___x_3013_);
lean_ctor_set(v___x_3252_, 3, v___x_3244_);
lean_ctor_set(v___x_3252_, 4, v___x_3251_);
v___x_3253_ = lean_st_mk_ref(v___x_3252_);
v___x_3254_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3228_, v_hasTrace_3020_, v___x_3248_, v___x_3253_, v___y_3016_, v___y_3017_);
lean_dec_ref_known(v___x_3248_, 7);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3254_, 1);
v___x_3256_ = lean_st_ref_get(v___x_3253_);
lean_dec(v___x_3253_);
lean_dec(v___x_3256_);
v___y_3171_ = v___x_3234_;
v___y_3172_ = v_a_3220_;
v___y_3173_ = v___x_3223_;
v___y_3174_ = v___x_3236_;
v_a_3175_ = v_a_3255_;
goto v___jp_3170_;
}
else
{
lean_dec(v___x_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3257_; 
v_a_3257_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3254_, 1);
v___y_3171_ = v___x_3234_;
v___y_3172_ = v_a_3220_;
v___y_3173_ = v___x_3223_;
v___y_3174_ = v___x_3236_;
v_a_3175_ = v_a_3257_;
goto v___jp_3170_;
}
else
{
lean_object* v_a_3258_; 
v_a_3258_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3254_, 1);
v___y_3154_ = v___x_3223_;
v___y_3155_ = v_a_3220_;
v_a_3156_ = v_a_3258_;
goto v___jp_3153_;
}
}
}
}
else
{
uint8_t v___x_3259_; uint8_t v___x_3260_; uint8_t v___x_3261_; lean_object* v___x_3262_; uint64_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_dec(v_snd_3229_);
v___x_3259_ = 1;
v___x_3260_ = 0;
v___x_3261_ = 2;
v___x_3262_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3262_, 0, v___x_3222_);
lean_ctor_set_uint8(v___x_3262_, 1, v___x_3222_);
lean_ctor_set_uint8(v___x_3262_, 2, v___x_3222_);
lean_ctor_set_uint8(v___x_3262_, 3, v___x_3222_);
lean_ctor_set_uint8(v___x_3262_, 4, v___x_3222_);
lean_ctor_set_uint8(v___x_3262_, 5, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 6, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 7, v___x_3222_);
lean_ctor_set_uint8(v___x_3262_, 8, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 9, v___x_3259_);
lean_ctor_set_uint8(v___x_3262_, 10, v___x_3260_);
lean_ctor_set_uint8(v___x_3262_, 11, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 12, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 13, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 14, v___x_3261_);
lean_ctor_set_uint8(v___x_3262_, 15, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 16, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 17, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 18, v___x_3234_);
lean_ctor_set_uint8(v___x_3262_, 19, v___x_3222_);
v___x_3263_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3262_);
v___x_3264_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set_uint64(v___x_3264_, sizeof(void*)*1, v___x_3263_);
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3267_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3268_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3269_ = lean_box(0);
lean_inc(v___x_3013_);
v___x_3270_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3270_, 0, v___x_3264_);
lean_ctor_set(v___x_3270_, 1, v___x_3013_);
lean_ctor_set(v___x_3270_, 2, v___x_3267_);
lean_ctor_set(v___x_3270_, 3, v___x_3268_);
lean_ctor_set(v___x_3270_, 4, v___x_3269_);
lean_ctor_set(v___x_3270_, 5, v___x_3265_);
lean_ctor_set(v___x_3270_, 6, v___x_3269_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*7, v___x_3222_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*7 + 1, v___x_3222_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*7 + 2, v___x_3222_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*7 + 3, v_hasTrace_3020_);
v___x_3271_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3272_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3273_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3271_);
lean_ctor_set(v___x_3274_, 1, v___x_3272_);
lean_ctor_set(v___x_3274_, 2, v___x_3013_);
lean_ctor_set(v___x_3274_, 3, v___x_3266_);
lean_ctor_set(v___x_3274_, 4, v___x_3273_);
v___x_3275_ = lean_st_mk_ref(v___x_3274_);
v___x_3276_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3228_, v___x_3270_, v___x_3275_, v___y_3016_, v___y_3017_);
lean_dec_ref_known(v___x_3270_, 7);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = lean_st_ref_get(v___x_3275_);
lean_dec(v___x_3275_);
lean_dec(v___x_3278_);
v___y_3165_ = v___x_3234_;
v___y_3166_ = v___x_3222_;
v___y_3167_ = v_a_3220_;
v___y_3168_ = v___x_3223_;
v_a_3169_ = v_a_3277_;
goto v___jp_3164_;
}
else
{
lean_dec(v___x_3275_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3279_; 
v_a_3279_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3276_, 1);
v___y_3165_ = v___x_3234_;
v___y_3166_ = v___x_3222_;
v___y_3167_ = v_a_3220_;
v___y_3168_ = v___x_3223_;
v_a_3169_ = v_a_3279_;
goto v___jp_3164_;
}
else
{
lean_object* v_a_3280_; 
v_a_3280_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3276_, 1);
v___y_3154_ = v___x_3223_;
v___y_3155_ = v_a_3220_;
v_a_3156_ = v_a_3280_;
goto v___jp_3153_;
}
}
}
}
}
else
{
lean_dec(v___x_3226_);
lean_dec(v_name_3015_);
lean_dec(v___x_3013_);
v___y_3159_ = v___x_3223_;
v___y_3160_ = v_a_3220_;
v_a_3161_ = v___x_3222_;
goto v___jp_3158_;
}
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v_env_3283_; lean_object* v___x_3284_; 
v___x_3281_ = lean_io_get_num_heartbeats();
v___x_3282_ = lean_st_ref_get(v___y_3017_);
v_env_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc_ref(v_env_3283_);
lean_dec(v___x_3282_);
lean_inc(v_name_3015_);
v___x_3284_ = l_Lean_Meta_declFromEqLikeName(v_env_3283_, v_name_3015_);
if (lean_obj_tag(v___x_3284_) == 1)
{
lean_object* v_val_3285_; lean_object* v_fst_3286_; lean_object* v_snd_3287_; lean_object* v___x_3288_; lean_object* v_env_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v_val_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_val_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v_fst_3286_ = lean_ctor_get(v_val_3285_, 0);
lean_inc_n(v_fst_3286_, 2);
v_snd_3287_ = lean_ctor_get(v_val_3285_, 1);
lean_inc_n(v_snd_3287_, 2);
lean_dec(v_val_3285_);
v___x_3288_ = lean_st_ref_get(v___y_3017_);
v_env_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc_ref(v_env_3289_);
lean_dec(v___x_3288_);
v___x_3290_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3289_, v_fst_3286_, v_snd_3287_);
v___x_3291_ = lean_name_eq(v_name_3015_, v___x_3290_);
lean_dec(v___x_3290_);
lean_dec(v_name_3015_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec(v_snd_3287_);
lean_dec(v_fst_3286_);
lean_dec(v___x_3013_);
v___x_3292_ = lean_box(0);
lean_inc(v___y_3017_);
lean_inc_ref(v___y_3016_);
v___x_3293_ = lean_apply_4(v___f_3014_, v___x_3292_, v___y_3016_, v___y_3017_, lean_box(0));
v___y_3212_ = v_a_3220_;
v___y_3213_ = v___x_3281_;
v___y_3214_ = v___x_3293_;
goto v___jp_3211_;
}
else
{
uint8_t v___x_3294_; 
lean_inc(v_snd_3287_);
v___x_3294_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_3287_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = ((lean_object*)(l_Lean_Meta_unfoldThmSuffix___closed__0));
v___x_3296_ = lean_string_dec_eq(v_snd_3287_, v___x_3295_);
lean_dec(v_snd_3287_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec(v_fst_3286_);
lean_dec(v___x_3013_);
v___x_3297_ = lean_box(0);
lean_inc(v___y_3017_);
lean_inc_ref(v___y_3016_);
v___x_3298_ = lean_apply_4(v___f_3014_, v___x_3297_, v___y_3016_, v___y_3017_, lean_box(0));
v___y_3212_ = v_a_3220_;
v___y_3213_ = v___x_3281_;
v___y_3214_ = v___x_3298_;
goto v___jp_3211_;
}
else
{
uint8_t v___x_3299_; uint8_t v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; uint64_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v___f_3014_);
v___x_3299_ = 1;
v___x_3300_ = 0;
v___x_3301_ = 2;
v___x_3302_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3302_, 0, v___x_3294_);
lean_ctor_set_uint8(v___x_3302_, 1, v___x_3294_);
lean_ctor_set_uint8(v___x_3302_, 2, v___x_3294_);
lean_ctor_set_uint8(v___x_3302_, 3, v___x_3294_);
lean_ctor_set_uint8(v___x_3302_, 4, v___x_3294_);
lean_ctor_set_uint8(v___x_3302_, 5, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 6, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 7, v___x_3294_);
lean_ctor_set_uint8(v___x_3302_, 8, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 9, v___x_3299_);
lean_ctor_set_uint8(v___x_3302_, 10, v___x_3300_);
lean_ctor_set_uint8(v___x_3302_, 11, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 12, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 13, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 14, v___x_3301_);
lean_ctor_set_uint8(v___x_3302_, 15, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 16, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 17, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 18, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, 19, v___x_3294_);
v___x_3303_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set_uint64(v___x_3304_, sizeof(void*)*1, v___x_3303_);
v___x_3305_ = lean_unsigned_to_nat(0u);
v___x_3306_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3307_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3309_ = lean_box(0);
lean_inc(v___x_3013_);
v___x_3310_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3310_, 0, v___x_3304_);
lean_ctor_set(v___x_3310_, 1, v___x_3013_);
lean_ctor_set(v___x_3310_, 2, v___x_3307_);
lean_ctor_set(v___x_3310_, 3, v___x_3308_);
lean_ctor_set(v___x_3310_, 4, v___x_3309_);
lean_ctor_set(v___x_3310_, 5, v___x_3305_);
lean_ctor_set(v___x_3310_, 6, v___x_3309_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7, v___x_3294_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 1, v___x_3294_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 2, v___x_3294_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*7 + 3, v___x_3222_);
v___x_3311_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3312_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3313_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3311_);
lean_ctor_set(v___x_3314_, 1, v___x_3312_);
lean_ctor_set(v___x_3314_, 2, v___x_3013_);
lean_ctor_set(v___x_3314_, 3, v___x_3306_);
lean_ctor_set(v___x_3314_, 4, v___x_3313_);
v___x_3315_ = lean_st_mk_ref(v___x_3314_);
v___x_3316_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fst_3286_, v___x_3222_, v___x_3310_, v___x_3315_, v___y_3016_, v___y_3017_);
lean_dec_ref_known(v___x_3310_, 7);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = lean_st_ref_get(v___x_3315_);
lean_dec(v___x_3315_);
lean_dec(v___x_3318_);
v___y_3195_ = v___x_3296_;
v___y_3196_ = v_a_3220_;
v___y_3197_ = v___x_3281_;
v___y_3198_ = v___x_3294_;
v_a_3199_ = v_a_3317_;
goto v___jp_3194_;
}
else
{
lean_dec(v___x_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3319_; 
v_a_3319_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3316_, 1);
v___y_3195_ = v___x_3296_;
v___y_3196_ = v_a_3220_;
v___y_3197_ = v___x_3281_;
v___y_3198_ = v___x_3294_;
v_a_3199_ = v_a_3319_;
goto v___jp_3194_;
}
else
{
lean_object* v_a_3320_; 
v_a_3320_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3316_, 1);
v___y_3207_ = v_a_3220_;
v___y_3208_ = v___x_3281_;
v_a_3209_ = v_a_3320_;
goto v___jp_3206_;
}
}
}
}
else
{
uint8_t v___x_3321_; uint8_t v___x_3322_; uint8_t v___x_3323_; uint8_t v___x_3324_; lean_object* v___x_3325_; uint64_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec(v_snd_3287_);
lean_dec_ref(v___f_3014_);
v___x_3321_ = 0;
v___x_3322_ = 1;
v___x_3323_ = 0;
v___x_3324_ = 2;
v___x_3325_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_3325_, 0, v___x_3321_);
lean_ctor_set_uint8(v___x_3325_, 1, v___x_3321_);
lean_ctor_set_uint8(v___x_3325_, 2, v___x_3321_);
lean_ctor_set_uint8(v___x_3325_, 3, v___x_3321_);
lean_ctor_set_uint8(v___x_3325_, 4, v___x_3321_);
lean_ctor_set_uint8(v___x_3325_, 5, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 6, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 7, v___x_3321_);
lean_ctor_set_uint8(v___x_3325_, 8, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 9, v___x_3322_);
lean_ctor_set_uint8(v___x_3325_, 10, v___x_3323_);
lean_ctor_set_uint8(v___x_3325_, 11, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 12, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 13, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 14, v___x_3324_);
lean_ctor_set_uint8(v___x_3325_, 15, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 16, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 17, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 18, v___x_3294_);
lean_ctor_set_uint8(v___x_3325_, 19, v___x_3321_);
v___x_3326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3325_);
v___x_3327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set_uint64(v___x_3327_, sizeof(void*)*1, v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
v___x_3330_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2, &l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3332_ = lean_box(0);
lean_inc(v___x_3013_);
v___x_3333_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3333_, 0, v___x_3327_);
lean_ctor_set(v___x_3333_, 1, v___x_3013_);
lean_ctor_set(v___x_3333_, 2, v___x_3330_);
lean_ctor_set(v___x_3333_, 3, v___x_3331_);
lean_ctor_set(v___x_3333_, 4, v___x_3332_);
lean_ctor_set(v___x_3333_, 5, v___x_3328_);
lean_ctor_set(v___x_3333_, 6, v___x_3332_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7, v___x_3321_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 1, v___x_3321_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 2, v___x_3321_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*7 + 3, v___x_3222_);
v___x_3334_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3335_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3336_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3334_);
lean_ctor_set(v___x_3337_, 1, v___x_3335_);
lean_ctor_set(v___x_3337_, 2, v___x_3013_);
lean_ctor_set(v___x_3337_, 3, v___x_3329_);
lean_ctor_set(v___x_3337_, 4, v___x_3336_);
v___x_3338_ = lean_st_mk_ref(v___x_3337_);
v___x_3339_ = l_Lean_Meta_getEqnsFor_x3f(v_fst_3286_, v___x_3333_, v___x_3338_, v___y_3016_, v___y_3017_);
lean_dec_ref_known(v___x_3333_, 7);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = lean_st_ref_get(v___x_3338_);
lean_dec(v___x_3338_);
lean_dec(v___x_3341_);
v___y_3201_ = v_a_3220_;
v___y_3202_ = v___x_3281_;
v___y_3203_ = v___x_3294_;
v_a_3204_ = v_a_3340_;
goto v___jp_3200_;
}
else
{
lean_dec(v___x_3338_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3342_; 
v_a_3342_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3339_, 1);
v___y_3201_ = v_a_3220_;
v___y_3202_ = v___x_3281_;
v___y_3203_ = v___x_3294_;
v_a_3204_ = v_a_3342_;
goto v___jp_3200_;
}
else
{
lean_object* v_a_3343_; 
v_a_3343_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3339_, 1);
v___y_3207_ = v_a_3220_;
v___y_3208_ = v___x_3281_;
v_a_3209_ = v_a_3343_;
goto v___jp_3206_;
}
}
}
}
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_dec(v___x_3284_);
lean_dec(v_name_3015_);
lean_dec(v___x_3013_);
v___x_3344_ = lean_box(0);
lean_inc(v___y_3017_);
lean_inc_ref(v___y_3016_);
v___x_3345_ = lean_apply_4(v___f_3014_, v___x_3344_, v___y_3016_, v___y_3017_, lean_box(0));
v___y_3212_ = v_a_3220_;
v___y_3213_ = v___x_3281_;
v___y_3214_ = v___x_3345_;
goto v___jp_3211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v___x_3459_, lean_object* v___f_3460_, lean_object* v_name_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___x_3459_, v___f_3460_, v_name_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = lean_unsigned_to_nat(3137104340u);
v___x_3511_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3512_ = l_Lean_Name_num___override(v___x_3511_, v___x_3510_);
return v___x_3512_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3515_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3516_ = l_Lean_Name_str___override(v___x_3515_, v___x_3514_);
return v___x_3516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3519_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3520_ = l_Lean_Name_str___override(v___x_3519_, v___x_3518_);
return v___x_3520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = lean_unsigned_to_nat(2u);
v___x_3522_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3523_ = l_Lean_Name_num___override(v___x_3522_, v___x_3521_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3525_; lean_object* v___x_3526_; 
v___f_3525_ = ((lean_object*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_));
v___x_3526_ = l_Lean_registerReservedNameAction(v___f_3525_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3527_; uint8_t v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec_ref_known(v___x_3526_, 1);
v___x_3527_ = ((lean_object*)(l_Lean_Meta_saveEqnAffectingOptions___closed__5));
v___x_3528_ = 0;
v___x_3529_ = lean_obj_once(&l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_, &l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
v___x_3530_ = l_Lean_registerTraceClass(v___x_3527_, v___x_3528_, v___x_3529_);
return v___x_3530_;
}
else
{
return v___x_3526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_3533_, lean_object* v_x_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3534_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_3539_, lean_object* v_x_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_3539_, v_x_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
return v_res_3544_;
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
